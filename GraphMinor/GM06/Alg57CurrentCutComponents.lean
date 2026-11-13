module

public import GraphMinor.GM06.Alg57CurrentCutOrigins
public import GraphMinor.GM06.Alg57CutComponentOrbit
import GraphMinor.Compute.GM06CutOriginFacts

/-!
# Component face inputs from the current drawing

The cut computation of VI (5.7), page 133, may scan the full original
vertex range. Unused slots are isolated and do not affect cuff-rooted
components. Every active copied origin lies in the computed vertex
list, and every copied row has one origin. Thus component face queries
have the same selected orbit as the full actual cut.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Every active computed origin is in the doubled original vertex
range and in the actual copied vertex list when the full range is scanned. -/
theorem cut_origins_valid :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
    ∀ d ∈ data.activeDarts,
      data.origins[d]?.getD 0 < 2 * x.vertexCount ∧
        data.origins[d]?.getD 0 ∈ data.vertices := by
  dsimp only
  intro d hd
  have ha := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hd
  have ho := cutOrigins_project_mem _ x.rotations rep.rows_flatten_nodup ha.2 ha.1
  refine ⟨by simpa only [gm06CutDataOfLinkage, rep.rows_length] using ho.1, ?_⟩
  apply cutOrigins_mem_vertices _ x.rotations _ rep.rows_flatten_nodup ha.2 ha.1
  intro v hv _
  exact List.mem_range.mpr (rep.rows_length ▸ hv)

/-- All copied ends in one current rotation row have exactly that
row's stored origin. -/
theorem cut_row_origins_eq (hG : IsCylinderSection5Drawing k G) (live : List ℕ) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations live
    ∀ row ∈ data.rotations, ∀ a ∈ row, ∀ b ∈ row,
      data.origins[a]?.getD 0 = data.origins[b]?.getD 0 := by
  dsimp only
  obtain ⟨hn, hk, _, _, _⟩ := rep.cut_data_face_encoding hG live
  intro row hr a ha b hb
  obtain ⟨v, hv, heq⟩ := List.mem_iff_getElem.mp hr
  have hz : (row, v) ∈ (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_some_iff.mpr ⟨hv, heq⟩
  have hab : a < 4 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
    have h := hk a (List.mem_flatten.mpr ⟨row, hr, ha⟩)
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
    omega
  have hbb : b < 4 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
    have h := hk b (List.mem_flatten.mpr ⟨row, hr, hb⟩)
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2]
    omega
  have hoa := gm06CutOrigins_getElem? _ row hn hz ha hab
  have hob := gm06CutOrigins_getElem? _ row hn hz hb hbb
  dsimp only [gm06CutDataOfLinkage] at hoa hob ⊢
  rw [hoa, hob]

/-- The reverse inner gap is an active end of the component rooted
at the positive inner gap. This uses only the computed origin and
paired ends, not a strip-component hypothesis. -/
theorem reverse_inner_in_component (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot data rep.tagged.length i.val ∧
      4 * (rep.tagged.length + i.val) + 1 ∈ (gm06CutComponentData data root).activeDarts := by
  dsimp only
  let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
    x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
  obtain ⟨hn, _, _, hc, hm⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hreverse : 4 * (rep.tagged.length + i.val) + 1 ∈ data.activeDarts := by
    have hh := (hc _).mpr (rep.reverse_inner_mem_cut hG i)
    have he : gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0 =
        4 * (rep.tagged.length + i.val) + 1 := by
      simp [gm06CutDart, Nat.add_div, Nat.add_mod]
    exact he ▸ hh
  have hpositive : 4 * (rep.tagged.length + i.val) ∈ data.activeDarts := by
    have hh := hm _ hreverse
    have he : gm06DartMate (4 * (rep.tagged.length + i.val) + 1) =
        4 * (rep.tagged.length + i.val) := by
      unfold gm06DartMate
      split_ifs <;> omega
    exact he ▸ hh
  have hv := rep.cut_origins_valid
  let root : Fin (2 * x.vertexCount) := ⟨_, (hv _ hpositive).1⟩
  have he : 4 * (rep.tagged.length + i.val) / 2 ∈ gm06CutComponentEdges data root := by
    apply (cutComponentEdges_iff_origin data root hm (fun d hd => (hv d hd).1)
      (fun d hd => (hv d hd).2) hpositive).mpr
    exact gm06CutComponentVertices_root_mem data root
  refine ⟨root, rfl, ?_⟩
  apply (gm06CutComponentData_active_iff data root _).mpr
  exact ⟨hreverse, by convert he using 1; omega⟩

/-- The cuff-rooted component face query returns exactly the full
computed cut's selected numeric orbit, with no representation premise. -/
theorem component_cut_face_row (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
    let m := 2 * (rep.tagged.length + (k + k))
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot data rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) m
        (gm06CutComponentData data root) (4 * (rep.tagged.length + i.val) + 1) =
          some (row, gm06IncV (2 * x.vertexCount) data.origins row, gm06IncE m row) ∧
        ∀ d : ℕ, d ∈ row ↔ ∃ j : ℕ,
          (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[j]
            (4 * (rep.tagged.length + i.val) + 1) = d := by
  dsimp only
  obtain ⟨root, hroot, ht⟩ := rep.reverse_inner_in_component hG i
  obtain ⟨hn, _, ha, hc, hm⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hv := rep.cut_origins_valid
  refine ⟨root, hroot, ?_⟩
  exact cutComponentFaceIncidence_orbit _ root hn hc hm ha
    (fun d hd => (hv d hd).1) (fun d hd => (hv d hd).2)
    (rep.cut_row_origins_eq hG _) ht

/-- The actual cuff-rooted component query reads region incidence
by projecting its returned copied darts, as in equation (10) of the
proof of VI (5.7). -/
theorem region_incidence_component_row (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) :
    let data := gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
    let m := 2 * (rep.tagged.length + (k + k))
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot data rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) m
        (gm06CutComponentData data root) (4 * (rep.tagged.length + i.val) + 1) =
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
  obtain ⟨root, hroot, row, hout, horbit⟩ := rep.component_cut_face_row hG i
  obtain ⟨oldrow, hold, hV, hE⟩ := rep.region_incidence_cut_row hk hG hno (List.range x.vertexCount) i
  obtain ⟨canonical, hcanonical, hcanonicalOrbit⟩ := rep.cut_face_row hG (List.range x.vertexCount) i
  have hsame : oldrow = canonical := by
    have hh : some (oldrow, gm06IncV (2 * x.vertexCount)
        (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
          x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)).origins oldrow,
        gm06IncE (2 * (rep.tagged.length + (k + k))) oldrow) =
        some (canonical, gm06IncV (2 * x.vertexCount)
        (gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints x.linkage
          x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)).origins canonical,
        gm06IncE (2 * (rep.tagged.length + (k + k))) canonical) := by
      exact hold.symm.trans hcanonical
    exact congrArg Prod.fst (Option.some.inj hh)
  have hcode : gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0 =
      4 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  have hset (q : ℕ) : q ∈ row ↔ q ∈ oldrow := by
    rw [hsame, horbit, hcanonicalOrbit, hcode]
  exact ⟨root, hroot, row, hout, by simpa only [← hset] using hV,
    by simpa only [← hset] using hE⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
