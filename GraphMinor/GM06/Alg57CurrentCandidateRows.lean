module

public import GraphMinor.GM06.Alg57EncodedReduction4Linkage
import GraphMinor.Compute.GM06CutDataBounds

/-!
# The actual candidate dart row

The candidate graph of VI (5.7), page 133, retains ordinary
face edges and deletes the opposite boundary and strict tail.
Its directed output therefore uses actual active cut darts.
The endpoint tests give the candidate vertex test at every
vertex of a nonempty output walk. These facts let projection
keep the exact directed row, including its edge labels.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Every vertex of a nonempty dart walk is an endpoint of one
of its darts, so endpoint properties hold on its whole vertex list. -/
theorem GM06DartWalk.vertices_of_endpoints {D V : Type*} {tail head : D → V}
    {s t : V} {ds : List D} (hw : GM06DartWalk tail head s ds t) (hne : ds ≠ [])
    {P : V → Prop} (hP : ∀ d ∈ ds, P (tail d) ∧ P (head d)) :
    ∀ v ∈ gm06WalkVertices head s ds, P v := by
  induction hw with
  | nil => exact absurd rfl hne
  | @cons s t d ds htail hwalk ih =>
    have hd := hP d List.mem_cons_self
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact htail ▸ hd.1
    · cases ds with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
        exact hv ▸ hd.2
      | cons e es =>
        exact ih (List.cons_ne_nil _ _) (fun q hq => hP q (List.mem_cons_of_mem _ hq)) v
          (by simpa only [gm06WalkVertices, List.map_cons] using hv)

/-- A candidate dart is incident at both its stored origin and
reverse origin with exactly the candidate vertex test. -/
theorem candidateDart_ends (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j d : ℕ)
    (hd : d ∈ gm06CandidateDarts m origins ordinary incV incE upper path j) :
    d < 2 * m ∧ ordinary[d / 2]?.getD false = true ∧ incE[d / 2]?.getD 0 ≠ 0 ∧
      gm06CandidateVertex incV upper path j (origins[d]?.getD 0) = true ∧
      gm06CandidateVertex incV upper path j (origins[gm06DartMate d]?.getD 0) = true := by
  obtain ⟨hdb, he⟩ := (gm06CandidateDarts_mem_iff _ _ _ _ _ _ _ _ _).mp hd
  obtain ⟨heb, hord, hinc, htail, hhead⟩ := (gm06CandidateEdges_mem_iff _ _ _ _ _ _ _ _).mp he
  rw [gm06CandidateEnds_length] at heb
  rw [gm06CandidateEnds_get origins heb] at htail hhead
  simp only at htail hhead
  refine ⟨hdb, hord, hinc, ?_⟩
  have hd := fun {a b : ℕ} (h : a = b) => congrArg (fun t => origins[t]?.getD 0) h
  rcases gm06DartMate_end_cases d with ⟨hpos, hneg⟩ | ⟨hpos, hneg⟩
  · rw [hd hpos, hd hneg]
    exact ⟨htail, hhead⟩
  · rw [hd hpos, hd hneg]
    exact ⟨hhead, htail⟩

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "edgeCount" => 2 * (rep.tagged.length + (k + k))
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i:arg => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0

/-- The complete copied origin table has its prescribed permanent size. -/
theorem cut_origin_table_length : (currentCut).origins.length = 2 * edgeCount := by
  have h := (gm06CutDataOfLinkage_sizes x.vertexCount rep.tagged.length x.endpoints x.linkage
    x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)).2.1
  rw [rep.cuff_lengths.1, rep.cuff_lengths.2] at h
  omega

/-- Every stored copied origin is in the permanent copied vertex space. -/
theorem cut_origin_table_bounds : ∀ v ∈ (currentCut).origins, v < 2 * x.vertexCount := by
  have hlen : x.endpoints.length = 2 * rep.tagged.length := by
    rw [rep.endpoints, gm06EndpointWords_length, List.length_map]
  have hi : ∀ v ∈ x.innerCuff, v < x.vertexCount := by
    intro v hv
    rw [rep.inner] at hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.source j).isLt
  have ho : ∀ v ∈ x.outerCuff, v < x.vertexCount := by
    intro v hv
    rw [rep.outer] at hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.target j).isLt
  exact gm06CutDataOfLinkage_origin_bounds _ _ _ _ _ _ rep.rows_length hlen
    (fun _ hv => rep.endpoint_word_lt hv) hi ho

/-- A successful canonical component query lists active darts
of the full cut, rather than only labels in the permanent range. -/
theorem component_query_row_active (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (root : Fin (2 * x.vertexCount))
    (hroot : root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val)
    (row : List ℕ)
    (hquery : gm06CutFaceIncidence (2 * x.vertexCount) edgeCount
      (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + i.val) + 1) =
      some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row, gm06IncE edgeCount row)) :
    ∀ d ∈ row, d ∈ (currentCut).activeDarts := by
  obtain ⟨root', hroot', row', hquery', horbit⟩ := rep.component_cut_face_row hG i
  have hr : root' = root := Fin.ext (hroot'.trans hroot.symm)
  subst root'
  have he : row' = row := congrArg Prod.fst (Option.some.inj (hquery'.symm.trans hquery))
  subst row'
  have hcode : gap i = 4 * (rep.tagged.length + i.val) + 1 := by simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  apply rep.cut_face_row_active hG (List.range x.vertexCount) i
  simpa only [hcode] using horbit

/-- Incidence of an edge means both of its directed ends are
active, since the actual face row is active and reversal preserves activity. -/
theorem incE_active (hG : IsCylinderSection5Drawing k G) (row : List ℕ)
    (hrow : ∀ r ∈ row, r ∈ (currentCut).activeDarts) (q : ℕ)
    (hinc : (gm06IncE edgeCount row)[q / 2]?.getD 0 ≠ 0) :
    q ∈ (currentCut).activeDarts := by
  obtain ⟨_, r, hr, hre⟩ := (incE_getD_ne_zero_iff _ _ _).mp hinc
  have hact := hrow r hr
  have hmate := (rep.cut_data_face_encoding hG (List.range x.vertexCount)).2.2.2.2 r hact
  have hsame : q = r ∨ q = gm06DartMate r := by
    rcases gm06DartMate_end_cases r with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩ <;>
      rcases gm06DartMate_end_cases q with ⟨hqpos, _⟩ | ⟨hqneg, _⟩ <;>
      omega
  exact hsame.elim (fun h => h ▸ hact) (fun h => h ▸ hmate)

/-- Every ordinary candidate dart is an active cut dart whose
projected word is an in-range ordinary edge word. -/
theorem candidate_dart_active (hG : IsCylinderSection5Drawing k G) (row : List ℕ)
    (hrow : ∀ r ∈ row, r ∈ (currentCut).activeDarts)
    (upper path : List ℕ) (j d : ℕ)
    (hd : d ∈ gm06CandidateDarts edgeCount (currentCut).origins
      (gm06CandidateOrdinary edgeCount rep.tagged.length)
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row) (gm06IncE edgeCount row) upper path j) :
    d ∈ (currentCut).activeDarts ∧ gm06UncutDart d < 2 * rep.tagged.length := by
  have hh := candidateDart_ends _ _ _ _ _ _ _ _ _ hd
  refine ⟨rep.incE_active hG row hrow d hh.2.2.1, ?_⟩
  rw [← cutOrdinaryFlags_eq_candidate] at hh
  have hord := (cutOrdinaryFlags_get _ _ _).mp hh.2.1
  unfold gm06UncutDart
  omega

end GM06CurrentDrawingRep
end GraphMinor.GM06
