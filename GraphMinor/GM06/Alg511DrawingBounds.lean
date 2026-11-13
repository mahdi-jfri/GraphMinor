module

public import GraphMinor.GM06.Alg511DrawingInput
public import GraphMinor.Compute.GM06Alg511GeometryTables
import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Bounds derived from the actual drawing input

The orientation programs for VI (5.11), page 134, scan directed
labels of the original graph with its two auxiliary cuff families.
Their label bounds follow from the geometric input correspondence.
A boundary step explicitly records one of its edge's two parameter
ends. A rotation row lists exactly the half-edges at its vertex.
Thus neither bound has to be supplied as an extra geometric fact.
The field lengths and augmented edge count are also bounded by the
ordinary graph and word-array sizes.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Each interpreted boundary word is one of the two directed labels
of an actual edge, including steps along loops. -/
theorem Alg511BoundaryDartsRep.labels_lt
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {m : ℕ}
    (edge : Fin m ≃ G.E) {γ : Set S → I → S} {φ : ℝ → S}
    {u v : S} (W : GraphWalk G.toGraph u v) :
    ∀ {a b : ℝ} {ds : List ℕ}, Alg511BoundaryDartsRep edge γ φ a b W ds →
      ∀ d ∈ ds, d < 2 * m := by
  induction W with
  | nil hu =>
    intro a b ds h
    cases ds with
    | nil => simp
    | cons _ _ => exact False.elim h
  | @cons u c v e he W ih =>
    intro a b ds h
    cases ds with
    | nil => exact False.elim h
    | cons d ds =>
      obtain ⟨_, _, _, _, _, _, _, hd, hrest⟩ := h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have hi := (edge.symm ⟨e, he.edge_mem⟩).isLt
        rcases hd with ⟨hd, _⟩ | ⟨hd, _⟩ <;> omega
      · exact ih hrest q hq

/-- Every word in a region boundary's walk tail has a valid directed
edge label. The region header is treated separately. -/
theorem Alg511RegionBoundaryRowRep.labels_lt
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {m : ℕ}
    {edge : Fin m ≃ G.E} {γ : Set S → I → S} {r : Set S}
    {C : Graph S (Set S)} {v : S} {W : GraphWalk G.toGraph v v} {ds : List ℕ}
    (h : Alg511RegionBoundaryRowRep edge γ r C W ds) : ∀ d ∈ ds, d < 2 * m := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, hds⟩
  · simp
  · exact hds.labels_lt edge W

/-- The serialized boundary rows retain exactly those valid walk
labels, after their first region-label word. -/
theorem Alg511RegionRowsRep.tail_labels_lt
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {G : Drawing S} {m r : ℕ} {edge : Fin m ≃ G.E} {γ : Set S → I → S}
    {region : Fin r → G.R} {rows : List (List ℕ)}
    (h : Alg511RegionRowsRep G edge γ region rows) :
    ∀ row ∈ rows, ∀ d ∈ row.tail, d < 2 * m := by
  obtain ⟨count, component, start, W, darts, rfl, hW⟩ := h
  intro row hrow
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hrow
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi
  rw [← hj]
  exact (hW i j).2.labels_lt

/-- All supplied rotation words and all region walk-tail words lie
in the directed range of the actual augmented drawing. -/
theorem GM06Alg511DrawingRep.drawing_labels_lt
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511DrawingRep x G) :
    (∀ row ∈ x.drawing.rotations, ∀ d ∈ row,
      d < 2 * (rep.graphTurn.graph.pairs.length + (x.drawing.pathCount + x.drawing.pathCount))) ∧
    (∀ row ∈ x.drawing.regionBoundaries, ∀ d ∈ row.tail,
      d < 2 * (rep.graphTurn.graph.pairs.length + (x.drawing.pathCount + x.drawing.pathCount))) := by
  obtain ⟨F, edge, γ, _, _, _, _, _, _, _, _, _, _, hlen, hrot, r, region, sphereRegion,
    _, hregions⟩ := rep.geometry
  change x.drawing.rotations.length = x.drawing.vertexCount at hlen
  constructor
  · intro row hrow d hd
    obtain ⟨i, hi, hrow⟩ := List.mem_iff_getElem.mp hrow
    have hin : i < x.drawing.vertexCount := by rw [← hlen]; exact hi
    let v : Fin x.drawing.vertexCount := ⟨i, hin⟩
    have hv := hrot v
    have hget : x.drawing.rotations.getD i [] = row := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hrow
    change Alg511CuffRotationRowRep edge γ (cylinderToSphere (rep.graphTurn.graph.vertex v).val)
      (x.drawing.rotations.getD i []) at hv
    rw [hget] at hv
    obtain ⟨a, ha⟩ := (hv.2.1 d).mp hd
    rw [← ha]
    exact halfEdgeLabel_lt edge a
  · exact hregions.tail_labels_lt

/-- The original pair count is read directly as half the endpoint
word count, independently of all geometric witnesses. -/
theorem GM06Alg511DrawingRep.pairCount_eq_half_endpoints
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511DrawingRep x G) :
    rep.graphTurn.graph.pairs.length = x.drawing.endpoints.length / 2 := by
  have h := congrArg List.length rep.graphTurn.graph.endpoints
  rw [gm06EndpointWords_length, List.length_map] at h
  change x.drawing.endpoints.length = 2 * rep.graphTurn.graph.pairs.length at h
  omega

/-- Both encoded geometry tables fit inside the supplied drawing
word array. This includes every region header and row length. -/
theorem GM06Alg511DrawingRep.geometry_lengths_le_input
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (_rep : GM06Alg511DrawingRep x G) :
    (gm06EncodeRows x.drawing.rotations).length ≤ (gm06Alg511Words x.drawing).length ∧
      (gm06EncodeRows x.drawing.regionBoundaries).length ≤ (gm06Alg511Words x.drawing).length := by
  constructor <;> apply gm06Alg511_encoded_row_length_le <;> simp [gm06Alg511Rows]

/-- The augmented dart range is linear in the ordinary vertex count
and supplied search-array length. Absolute winding integers do not
enter this purely combinatorial bound. -/
theorem GM06Alg511DrawingRep.augmented_darts_le_four_size
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511DrawingRep x G) (hk : 0 < x.drawing.pathCount) :
    2 * (rep.graphTurn.graph.pairs.length + (x.drawing.pathCount + x.drawing.pathCount)) ≤
      4 * (x.drawing.vertexCount + (gm06Alg511SearchWords x).length) := by
  have hpairs := rep.pairCount_eq_half_endpoints
  have hkV := rep.graphTurn.pathCount_le_vertexCount hk
  have hE : x.drawing.endpoints.length ≤ (gm06Alg511Words x.drawing).length :=
    gm06Alg511_encoded_row_length_le (by simp [gm06Alg511Rows])
  have hB : (gm06Alg511Words x.drawing).length ≤ (gm06Alg511WindingWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp)
  have hW : (gm06Alg511WindingWords x).length ≤ (gm06Alg511SearchWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp [gm06Alg511SearchRows])
  omega

/-- On an actual supplied drawing input, the full reflected-geometry
program needs no assumed dart bounds. They follow from the input
correspondence. Its word width is logarithmic in the graph-plus-input
size; the supplied integer words must also fit that width. -/
theorem alg511_reflect_geometryTables_exec {w : ℕ}
    (x : GM06Alg511WindingInput) {G : Drawing ClosedCylinder}
    (rep : GM06Alg511DrawingRep x G) (hk : 0 < x.drawing.pathCount)
    (s : State)
    (hwidth : wordSize 2 (x.drawing.vertexCount + (gm06Alg511SearchWords x).length) ≤ w)
    (hwords : ∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w)
    (h1002 : s.arrs 1002 = gm06Alg511Words x.drawing)
    (h3 : s.arrs 3 = x.drawing.endpoints) (h52 : s.regs 52 = x.drawing.pathCount) :
    ∃ s' t, Exec w gm06Alg511ReflectGeometryTablesProg s s' t ∧
      t ≤ 3000 * (x.drawing.vertexCount + (gm06Alg511SearchWords x).length + 1) ^ 2 ∧
      TwoPaths.Keeps [60, 31, 7, 8, 9, 11, 20, 23, 24, 323, 324, 313, 98, 1400, 1401]
        [4, 25, 26, 27, 28, 1220, 1221] s s' ∧
      s'.regs 60 = rep.graphTurn.graph.pairs.length ∧
      s'.arrs 1220 = gm06EncodeRows x.reflected.drawing.rotations ∧
      s'.arrs 1221 = gm06EncodeRows x.reflected.drawing.regionBoundaries := by
  let N := x.drawing.vertexCount + (gm06Alg511SearchWords x).length
  have hsq : (N + 2) ^ 2 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (by decide : 1 ≤ 2) N).trans_le
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hwidth)
  have hlin : 4 * N ≤ (N + 2) ^ 2 := by nlinarith
  have hlinear : 4 * N < 2 ^ w := hlin.trans_lt hsq
  have htwo : (2 : ℕ) ^ 2 ≤ (N + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hw : 2 < 2 ^ w := by norm_num at htwo; omega
  have hB : (gm06Alg511Words x.drawing).length ≤ (gm06Alg511WindingWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp)
  have hW : (gm06Alg511WindingWords x).length ≤ (gm06Alg511SearchWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp [gm06Alg511SearchRows])
  have hBN : (gm06Alg511Words x.drawing).length ≤ N := by dsimp [N]; omega
  have hbase : ∀ v ∈ gm06Alg511Words x.drawing, v < 2 ^ w := by
    intro v hv
    have hvW : v ∈ gm06Alg511WindingWords x := gm06Alg511_mem_encoded_row (by simp) hv
    exact hwords v (gm06Alg511_mem_encoded_row (by simp [gm06Alg511SearchRows]) hvW)
  have haug := (rep.augmented_darts_le_four_size hk).trans_lt hlinear
  have hpair := rep.pairCount_eq_half_endpoints
  rw [hpair] at haug
  obtain ⟨hrot, hregion⟩ := rep.drawing_labels_lt
  rw [hpair] at hrot hregion
  obtain ⟨s', t, he, ht, hkeep, hm, hrotOut, hregionOut⟩ :=
    gm06Alg511ReflectGeometryTablesProg_exec x.drawing s hw (by omega) hbase
      (by simpa only [Nat.add_assoc] using haug)
      (by simpa only [Nat.add_assoc] using hrot)
      (by simpa only [Nat.add_assoc] using hregion) h1002 h3 h52
  refine ⟨s', t, he, ht.trans (Nat.mul_le_mul_left 3000
    (Nat.pow_le_pow_left (Nat.add_le_add_right hBN 1) 2)), hkeep, hm.trans hpair.symm, hrotOut, hregionOut⟩

end GraphMinor.GM06
