module

public import GraphMinor.Compute.GM06Reduction4Phase
public import GraphMinor.Compute.GM06CutAlongLinkageProgram
import GraphMinor.Compute.GM06CutAdjacencyMath

/-!
# Finite encoding facts for the phase's computed components

Sections 9 to 12 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) pass
induced cut components to face enumeration and candidate searches.
Filtering complete edges preserves their paired ends and unique
origins. Filtering the increasing active list gives the canonical
active list of the induced rotations. These facts are derived for
the actual pure phase components, rather than assumed by its caller.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restricting to complete edge labels pairs every retained dart,
even if the ambient active list omitted one end of some other edge. -/
theorem gm06CutInducedByVertices_mate_closed (data : GM06CutData) (vertices : List ℕ) :
    ∀ d ∈ (gm06CutInducedByVertices data vertices).activeDarts,
      gm06DartMate d ∈ (gm06CutInducedByVertices data vertices).activeDarts := by
  intro d hd
  simp only [gm06CutInducedByVertices, List.mem_filter, decide_eq_true_eq] at hd ⊢
  have hedge := (gm06CutEdgeLabels_mem_iff data (d / 2)).mp hd.2.1
  have hmate : gm06DartMate d ∈ data.activeDarts := by
    rcases gm06DartMate_end_cases d with ⟨_, hm⟩ | ⟨_, hm⟩
    · exact hm ▸ hedge.2
    · exact hm ▸ hedge.1
  exact ⟨hmate, by simpa only [gm06DartMate_edge] using hd.2⟩

/-- Canonical increasing active-end order is preserved by restriction
to any explicit vertex set. -/
theorem gm06CutInducedByVertices_canonical {q : ℕ} (data : GM06CutData) (vertices : List ℕ)
    (hcanon : data.activeDarts = (List.range q).filter (fun d => decide (d ∈ data.rotations.flatten))) :
    (gm06CutInducedByVertices data vertices).activeDarts =
      (List.range q).filter (fun d => decide (d ∈ (gm06CutInducedByVertices data vertices).rotations.flatten)) := by
  let edges := (gm06CutEdgeLabels data).filter (fun e => decide
    ((gm06CutEndpoints data e).1 ∈ vertices ∧ (gm06CutEndpoints data e).2 ∈ vertices))
  let keep := fun d => decide (d / 2 ∈ edges)
  have ha : (gm06CutInducedByVertices data vertices).activeDarts = data.activeDarts.filter keep := rfl
  have hr : (gm06CutInducedByVertices data vertices).rotations.flatten = data.rotations.flatten.filter keep := by
    simp only [gm06CutInducedByVertices, List.filter_flatten, edges, keep]
  rw [ha, hcanon, hr, List.filter_filter]
  apply List.filter_congr
  intro d _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_filter]
  tauto

/-- The phase always returns one component record per inner cuff gap. -/
theorem gm06PhaseComponents_length (x : GM06SuccessorInput) (m : ℕ) :
    (gm06PhaseComponents x m).length = x.innerCuff.length := by
  simp only [gm06PhaseComponents, gm06CutAlongLinkage, List.length_map,
    gm06CutCuffMembership, gm06CutComponentBitsFrom_length]

/-- Every computed component has canonical active labels, paired
ends, the original shared origin table, and repetition-free rotations. -/
theorem gm06PhaseComponents_encoding {m : ℕ} (x : GM06SuccessorInput)
    (hnd : x.rotations.flatten.Nodup) (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    let data := gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
      x.rotations (List.range x.vertexCount)
    part.rotations.length = data.rotations.length ∧ part.origins = data.origins ∧
      part.rotations.flatten.Sublist data.rotations.flatten ∧ part.rotations.flatten.Nodup ∧
      part.activeDarts = (List.range (4 * (m + x.innerCuff.length + x.outerCuff.length))).filter
        (fun d => decide (d ∈ part.rotations.flatten)) ∧
      ∀ d ∈ part.activeDarts, gm06DartMate d ∈ part.activeDarts := by
  dsimp only
  obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hp
  let data := gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount)
  let vertices := gm06CutBitVertices (2 * x.vertexCount) bits
  have hsub : (gm06CutInducedByVertices data vertices).rotations.flatten.Sublist data.rotations.flatten := by
    unfold gm06CutInducedByVertices
    rw [← List.filter_flatten]
    exact List.filter_sublist
  have hdataNd : data.rotations.flatten.Nodup := gm06SplitRotationRows_nodup _ _ hnd
  exact ⟨List.length_map _, rfl, hsub, hdataNd.sublist hsub,
    gm06CutInducedByVertices_canonical data vertices rfl, gm06CutInducedByVertices_mate_closed data vertices⟩

/-- Every component has one permanent row per copied vertex and the
same bounded origin table. These are input facts for the face/search passes. -/
theorem gm06PhaseComponents_sizes {m : ℕ} (x : GM06SuccessorInput)
    (hrows : x.rotations.length = x.vertexCount) (horig : x.endpoints.length = 2 * m)
    (hv : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hci : ∀ v ∈ x.innerCuff, v < x.vertexCount) (hco : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    part.rotations.length = 2 * x.vertexCount ∧
      part.origins.length = 4 * (m + x.innerCuff.length + x.outerCuff.length) ∧
      (∀ v ∈ part.origins, v < 2 * x.vertexCount) ∧
      ∀ d ∈ part.rotations.flatten, d < 4 * (m + x.innerCuff.length + x.outerCuff.length) := by
  obtain ⟨hlen, ho, hsub, _⟩ := gm06PhaseComponents_encoding x hnd part hp
  have hs := gm06CutDataOfLinkage_sizes x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount)
  have hb := gm06CutDataOfLinkage_dart_bounds (n := x.vertexCount) x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount) hkeys
  refine ⟨by rw [hlen, hs.1, hrows], by rw [ho, hs.2.1], ?_, fun d hd => hb.1 d (hsub.subset hd)⟩
  rw [ho]
  exact gm06CutDataOfLinkage_origin_bounds x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations
    (List.range x.vertexCount) hrows horig hv hci hco

/-- Every component's origin lookup names exactly its row. This
supplies the unique-origin premise of the actual candidate CSR builder. -/
theorem gm06PhaseComponents_origin_row_iff {m : ℕ} (x : GM06SuccessorInput)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    ∀ d ∈ part.rotations.flatten, ∀ v : Fin (2 * x.vertexCount),
      part.origins[d]?.getD 0 = v.val ↔ d ∈ part.rotations[v.val]?.getD [] := by
  obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hp
  let data := gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount)
  let vertices := gm06CutBitVertices (2 * x.vertexCount) bits
  let edges := (gm06CutEdgeLabels data).filter (fun e => decide
    ((gm06CutEndpoints data e).1 ∈ vertices ∧ (gm06CutEndpoints data e).2 ∈ vertices))
  let keep := fun d => decide (d / 2 ∈ edges)
  intro d hd v
  have hd' : d ∈ data.rotations.flatten.filter keep := by
    simpa only [gm06CutInducedByVertices, List.filter_flatten, data, vertices, edges, keep] using hd
  obtain ⟨hdOrig, hkeep⟩ := List.mem_filter.mp hd'
  have hactive : d ∈ data.activeDarts := by
    apply (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ d).mpr
    exact ⟨(gm06CutDataOfLinkage_dart_bounds (n := x.vertexCount) x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations
      (List.range x.vertexCount) hkeys).1 d hdOrig, hdOrig⟩
  have hv : v.val < data.rotations.length := by
    simp only [data, gm06CutDataOfLinkage, gm06SplitRotationRows_length, hrows]
    exact v.isLt
  have hrow : (gm06CutInducedByVertices data vertices).rotations[v.val]?.getD [] =
      (data.rotations[v.val]).filter keep := by
    simp only [gm06CutInducedByVertices, List.getElem?_map, List.getElem?_eq_getElem hv,
      Option.map_some, Option.getD_some, edges, keep]
  change data.origins[d]?.getD 0 = v.val ↔ d ∈ (gm06CutInducedByVertices data vertices).rotations[v.val]?.getD []
  rw [hrow]
  have hiff := gm06CutDataOfLinkage_origin_row_iff x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations
    (List.range x.vertexCount) hrows hnd hactive v.isLt
  change data.origins[d]?.getD 0 = v.val ↔ d ∈ data.rotations[v.val]?.getD [] at hiff
  simpa only [List.mem_filter, hkeep, and_true, List.getElem?_eq_getElem hv, Option.getD_some] using hiff

end GraphMinor.Compute
