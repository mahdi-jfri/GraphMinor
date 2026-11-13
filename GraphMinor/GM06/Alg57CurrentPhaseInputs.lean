module

public import GraphMinor.GM06.Alg57CurrentTerminalRep
public import GraphMinor.Compute.GM06Reduction4Phase
import GraphMinor.Compute.GM06CutAlongLinkageProgram

/-!
# The actual finite phase inputs

The complete phase programs for VI (5.7), page 133, use numeric
copied boundary lists and their actual cuff-indexed component
records. The current drawing interpretation makes these exactly
the bounded path lists and component data used by the geometric
representation proofs. This file proves those equalities directly
from the endpoint, path and cuff arrays.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- The ordinary flags of the complete phase are the same flags
used in the current geometric edge interpretation. -/
theorem cutOrdinaryFlags_eq_candidate (m k : ℕ) :
    gm06CutOrdinaryFlags m k = gm06CandidateOrdinary (2 * (m + (k + k))) m := by
  apply List.ext_getElem
  · simp only [gm06CutOrdinaryFlags, gm06CandidateOrdinary, List.length_ofFn,
      List.length_map, List.length_range]
  · intro e he he'
    simp only [gm06CutOrdinaryFlags, gm06CandidateOrdinary, List.getElem_ofFn,
      List.getElem_map, List.getElem_range]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)

/-- The complete phase's next index is the linkage's cyclic successor. -/
theorem phase_next_eq (i : Fin k) : gm06PhaseNext x i.val = (finSuccCycle i).val := by
  simp only [gm06PhaseNext, rep.cuff_lengths.1, finSuccCycle]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : i.val + 1 = k := by have hi := i.isLt; omega
    rw [he, Nat.mod_self]

/-- The bounded copied steps have exactly the numeric edge and
arrival words loaded by the complete phase. -/
theorem computed_path_steps_phase (hn : 0 < x.vertexCount) (i : Fin k) :
    (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true).map
      (fun p => (p.1, p.2.val)) = gm06PhaseLeftSteps x i.val := by
  simp only [gm06CutPathSteps, gm06PhaseLeftSteps, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro d hd
  have hi : i.val < x.linkage.length := by rw [rep.linkage.1]; exact i.isLt
  have hd' : d ∈ x.linkage[i.val] := by
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hd
  have hflat := List.mem_flatten.mpr ⟨_, List.getElem_mem hi, hd'⟩
  have hb : x.endpoints[gm06DartMate d]?.getD 0 < x.vertexCount := rep.cut_path_origin_lt true hflat
  apply Prod.ext
  · have hm := Nat.mod_lt d (by decide : 0 < 2)
    simp only [Bool.not_true, Bool.toNat_false, gm06CutDart]
    omega
  · rw [cutVertexFin_val hn hb true]
    rfl

/-- The bounded copied path labels have exactly the numeric
boundary words used by the actual phase programs. -/
theorem computed_path_labels_phase (hn : 0 < x.vertexCount) (i : Fin k) (left : Bool) :
    (gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD [])
      (x.innerCuff[i.val]?.getD 0) left).map Fin.val = gm06PhaseBoundaryVertices x i.val (!left).toNat := by
  have hs : x.innerCuff[i.val]?.getD 0 = (rep.source i).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have hsource : x.innerCuff[i.val]?.getD 0 < x.vertexCount := by rw [hs]; exact (rep.source i).isLt
  simp only [gm06CutPathLabels, find4PathLabels, gm06CutPathSteps, gm06PhaseBoundaryVertices,
    List.map_cons, List.map_map, Function.comp_def]
  congr 1
  · rw [cutVertexFin_val hn hsource left]
    rfl
  · apply List.map_congr_left
    intro d hd
    have hi : i.val < x.linkage.length := by rw [rep.linkage.1]; exact i.isLt
    have hd' : d ∈ x.linkage[i.val] := by
      simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hd
    have hflat := List.mem_flatten.mpr ⟨_, List.getElem_mem hi, hd'⟩
    have hb : x.endpoints[gm06DartMate d]?.getD 0 < x.vertexCount := rep.cut_path_origin_lt true hflat
    rw [cutVertexFin_val hn hb left]
    rfl

/-- The component actually returned at an inner cuff index is the
component at its prescribed positive-inner-end root. -/
theorem phase_component_at (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    ∃ root : Fin (2 * x.vertexCount), root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val ∧
      (gm06PhaseComponents x rep.tagged.length)[i.val]? = some (gm06CutComponentData currentCut root) := by
  obtain ⟨root, hroot, _⟩ := rep.reverse_inner_in_component hG i
  have hlen : x.endpoints.length = 2 * rep.tagged.length := by
    rw [rep.endpoints, gm06EndpointWords_length, List.length_map]
  have hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount := by
    intro v hv
    rw [rep.inner] at hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.source j).isLt
  have houter : ∀ v ∈ x.outerCuff, v < x.vertexCount := by
    intro v hv
    rw [rep.outer] at hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.target j).isLt
  have hall := gm06CutAlongLinkage_components x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount) rep.rows_length hlen (fun _ hv => rep.endpoint_word_lt hv) hinner houter
  change (gm06PhaseComponents x rep.tagged.length).map some =
    gm06CutComponents (2 * x.vertexCount) rep.tagged.length x.innerCuff.length currentCut at hall
  have hg := congrArg (fun rows => rows[i.val]?) hall
  have hrootBound : gm06CutInnerRoot currentCut rep.tagged.length i.val < 2 * x.vertexCount :=
    hroot ▸ root.isLt
  simp only [List.getElem?_map, gm06CutComponents,
    List.getElem?_range, rep.cuff_lengths.1, i.isLt, Option.map_some,
    gm06CutComponentAt_eq_some _ hrootBound] at hg
  obtain ⟨part, hpart, hpartEq⟩ := Option.map_eq_some_iff.mp hg
  have hpartRoot : part = gm06CutComponentData currentCut root := by
    have he := Option.some.inj hpartEq
    have hfin : (⟨gm06CutInnerRoot currentCut rep.tagged.length i.val, hrootBound⟩ : Fin (2 * x.vertexCount)) = root :=
      Fin.ext hroot.symm
    simpa only [hfin] using he
  exact ⟨root, hroot, hpartRoot ▸ hpart⟩

/-- The actual cuff-indexed phase search is the directed FIND_4
query whose arrays satisfy the geometric representation. -/
theorem phase_find4_rep (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) :
    ∃ row : List ℕ,
      gm06Reduction4PhaseAt x rep.tagged.length i.val =
        gm06Find4Darts (2 * (rep.tagged.length + (k + k))) (currentCut).origins
          (gm06CandidateOrdinary (2 * (rep.tagged.length + (k + k))) rep.tagged.length)
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
          (gm06IncE (2 * (rep.tagged.length + (k + k))) row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
          (gm06CutVertexFin x.vertexCount hn (x.innerCuff[i.val]?.getD 0) true)
          (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true) ∧
      Find4Rep L i (gm06CandidateEnds (2 * (rep.tagged.length + (k + k))) (currentCut).origins)
          (gm06CandidateOrdinary (2 * (rep.tagged.length + (k + k))) rep.tagged.length)
          (gm06IncV (2 * x.vertexCount) (currentCut).origins row)
          (gm06IncE (2 * (rep.tagged.length + (k + k))) row)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
          (gm06CutVertexFin x.vertexCount hn (x.innerCuff[i.val]?.getD 0) true)
          (gm06CutPathSteps x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD []) true)
          rep.cutVertexPoint rep.cutEdgePoint := by
  obtain ⟨root, hroot, row, hquery, hrep⟩ := rep.component_find4_rep hn hk hG hno i
  obtain ⟨root', hroot', hpart⟩ := rep.phase_component_at hG i
  have he : root' = root := Fin.ext (hroot'.trans hroot.symm)
  subst root'
  have hupper := rep.computed_path_labels_phase hn (finSuccCycle i) false
  simp only [Bool.not_false, Bool.toNat_true] at hupper
  rw [cutOrdinaryFlags_eq_candidate, hupper, ← rep.phase_next_eq i] at hrep
  refine ⟨row, ?_, hrep⟩
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

end GM06CurrentDrawingRep
end GraphMinor.GM06
