module

public import GraphMinor.Compute.GM06CutCuffSearch

/-!
# Finite membership rows for cuff-indexed cut components

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) searches each
component through its inner cuff edge. A search returns a dense row
of reached vertices. This file gives its exact list function and
proves how that row selects the vertices, edge labels and induced
rotation rows of the component. These interpretations use membership
bits only and perform no reachability search themselves.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Membership row of the component at one inner cuff edge.
An out-of-range root gives an empty row. -/
def gm06CutComponentBitsAt (n : ℕ) (data : GM06CutData) (m i : ℕ) : List ℕ :=
  if h : gm06CutInnerRoot data m i < n then
    gm06ComponentBits (gm06CutGraph n data) ⟨gm06CutInnerRoot data m i, h⟩ else []

/-- Membership rows in consecutive inner cuff-gap order. -/
def gm06CutComponentBitsFrom (n : ℕ) (data : GM06CutData) (m : ℕ) : ℕ → ℕ → List (List ℕ)
  | _, 0 => []
  | base, k + 1 => gm06CutComponentBitsAt n data m base :: gm06CutComponentBitsFrom n data m (base + 1) k

/-- A valid cuff root gives the exact complete component bitmap. -/
theorem gm06CutComponentBitsAt_eq {n m i : ℕ} (data : GM06CutData)
    (hr : gm06CutInnerRoot data m i < n) :
    gm06CutComponentBitsAt n data m i =
      gm06ComponentBits (gm06CutGraph n data) ⟨gm06CutInnerRoot data m i, hr⟩ := by
  simp only [gm06CutComponentBitsAt, dite_eq_left hr]

/-- A membership row has one bit per vertex, unless its root is invalid. -/
theorem gm06CutComponentBitsAt_length_le (n : ℕ) (data : GM06CutData) (m i : ℕ) :
    (gm06CutComponentBitsAt n data m i).length ≤ n := by
  unfold gm06CutComponentBitsAt
  split_ifs <;> simp [gm06ComponentBits]

/-- Every output field of a component membership row is zero or one. -/
theorem gm06CutComponentBitsAt_words (n : ℕ) (data : GM06CutData) (m i : ℕ) :
    ∀ x ∈ gm06CutComponentBitsAt n data m i, x = 0 ∨ x = 1 := by
  unfold gm06CutComponentBitsAt
  split_ifs
  · intro x hx
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
    split_ifs <;> simp
  · simp

/-- The root belongs to every valid returned membership row. -/
theorem gm06CutComponentBitsAt_root {n m i : ℕ} (data : GM06CutData)
    (hr : gm06CutInnerRoot data m i < n) :
    (gm06CutComponentBitsAt n data m i)[gm06CutInnerRoot data m i]?.getD 0 = 1 := by
  simp only [gm06CutComponentBitsAt_eq data hr, gm06ComponentBits,
    List.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some]
  exact ite_eq_left (SimpleGraph.Reachable.refl _)

/-- One row is returned per requested cuff gap. -/
theorem gm06CutComponentBitsFrom_length (n : ℕ) (data : GM06CutData) (m base k : ℕ) :
    (gm06CutComponentBitsFrom n data m base k).length = k := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih => simp only [gm06CutComponentBitsFrom, List.length_cons, ih]

/-- Membership-row serialization has at most k*(n+1) words. -/
theorem gm06CutComponentBitsFrom_payload_length_le (n : ℕ) (data : GM06CutData) (m base k : ℕ) :
    (gm06EncodeRowsPayload (gm06CutComponentBitsFrom n data m base k)).length ≤ k * (n + 1) := by
  induction k generalizing base with
  | zero => simp [gm06CutComponentBitsFrom, gm06EncodeRowsPayload]
  | succ k ih =>
    have hb := gm06CutComponentBitsAt_length_le n data m base
    have ht := ih (base + 1)
    simp only [gm06EncodeRowsPayload] at ht
    simp only [gm06CutComponentBitsFrom, gm06EncodeRowsPayload, List.flatMap_cons,
      List.length_append, gm06EncodeNatList, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Every row in a consecutive cuff search has zero/one fields. -/
theorem gm06CutComponentBitsFrom_words (n : ℕ) (data : GM06CutData) (m base k : ℕ) :
    ∀ bits ∈ gm06CutComponentBitsFrom n data m base k, ∀ x ∈ bits, x = 0 ∨ x = 1 := by
  induction k generalizing base with
  | zero => simp [gm06CutComponentBitsFrom]
  | succ k ih =>
    intro bits hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact gm06CutComponentBitsAt_words n data m base
    · exact ih (base + 1) bits hb

/-- Valid cuff roots give one bit per permanent vertex in every row. -/
theorem gm06CutComponentBitsFrom_row_lengths (n : ℕ) (data : GM06CutData) (m base k : ℕ)
    (hroots : ∀ i, base ≤ i → i < base + k → gm06CutInnerRoot data m i < n) :
    ∀ bits ∈ gm06CutComponentBitsFrom n data m base k, bits.length = n := by
  induction k generalizing base with
  | zero => simp [gm06CutComponentBitsFrom]
  | succ k ih =>
    intro bits hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rw [gm06CutComponentBitsAt_eq data (hroots base le_rfl (by omega))]
      simp only [gm06ComponentBits, List.length_ofFn]
    · exact ih (base + 1) (fun i hlo hhi => hroots i (by omega) (by omega)) bits hb

/-- Read a membership row as permanent vertex labels, in increasing order. -/
def gm06CutBitVertices (n : ℕ) (bits : List ℕ) : List ℕ :=
  ((List.finRange n).filter (fun v => bits[v.val]?.getD 0 == 1)).map Fin.val

/-- Reading the returned bits yields precisely the finite component vertices. -/
theorem gm06CutBitVertices_eq {n : ℕ} (data : GM06CutData) (root : Fin n) :
    gm06CutBitVertices n (gm06ComponentBits (gm06CutGraph n data) root) = gm06CutComponentVertices data root := by
  unfold gm06CutBitVertices gm06CutComponentVertices
  congr 1
  apply List.filter_congr
  intro v _
  simp only [gm06ComponentBits, List.getElem?_ofFn, v.isLt, ↓reduceDIte, Option.getD_some]
  by_cases h : (gm06CutGraph n data).Reachable root v <;> simp only [h, ↓reduceIte, decide_true, decide_false] <;> rfl

/-- Restrict the stored graph to an explicit vertex list. No search
or geometric assertion is used in this data interpretation. -/
def gm06CutInducedByVertices (data : GM06CutData) (vertices : List ℕ) : GM06CutData :=
  let edges := (gm06CutEdgeLabels data).filter (fun e => decide
    ((gm06CutEndpoints data e).1 ∈ vertices ∧ (gm06CutEndpoints data e).2 ∈ vertices))
  let keep := fun d => decide (d / 2 ∈ edges)
  { rotations := data.rotations.map (List.filter keep)
    origins := data.origins
    activeDarts := data.activeDarts.filter keep
    vertices := vertices }

/-- The interpretation keeps exactly the component's induced rotations,
origins and active edge ends, as well as its reached vertices. -/
theorem gm06CutInducedByVertices_component {n : ℕ} (data : GM06CutData) (root : Fin n) :
    gm06CutInducedByVertices data (gm06CutComponentVertices data root) = gm06CutComponentData data root := rfl

/-- Restricting to retained complete edges pairs every component dart,
even if the ambient input had an incomplete edge. -/
theorem gm06CutComponentData_mate_closed {n : ℕ} (data : GM06CutData) (root : Fin n) :
    ∀ d ∈ (gm06CutComponentData data root).activeDarts,
      gm06DartMate d ∈ (gm06CutComponentData data root).activeDarts := by
  intro d hd
  obtain ⟨_, hedge⟩ := (gm06CutComponentData_active_iff data root d).mp hd
  have hpair := (gm06CutEdgeLabels_mem_iff data (d / 2)).mp
    ((gm06CutComponentEdges_mem_iff data root (d / 2)).mp hedge).1
  apply (gm06CutComponentData_active_iff data root (gm06DartMate d)).mpr
  refine ⟨?_, by simpa only [gm06DartMate_edge] using hedge⟩
  rcases gm06DartMate_end_cases d with ⟨_, hm⟩ | ⟨_, hm⟩
  · simpa only [hm] using hpair.2
  · simpa only [hm] using hpair.1

/-- Decode one dense membership row as its induced finite component. -/
def gm06DecodeCutComponentBitsAt (n : ℕ) (data : GM06CutData) (m i : ℕ) (bits : List ℕ) : Option GM06CutData :=
  if gm06CutInnerRoot data m i < n ∧ bits.length = n then
    some (gm06CutInducedByVertices data (gm06CutBitVertices n bits)) else none

/-- The bit-row interpretation is the exact pure component output. -/
theorem gm06DecodeCutComponentBitsAt_eq (n : ℕ) (data : GM06CutData) (m i : ℕ) :
    gm06DecodeCutComponentBitsAt n data m i (gm06CutComponentBitsAt n data m i) =
      gm06CutComponentAt n data (gm06CutInnerRoot data m i) := by
  by_cases hr : gm06CutInnerRoot data m i < n
  · simp only [gm06DecodeCutComponentBitsAt, gm06CutComponentBitsAt_eq data hr,
      gm06ComponentBits, List.length_ofFn, hr, and_self, ↓reduceIte]
    rw [show List.ofFn (fun v => if (gm06CutGraph n data).Reachable
        ⟨gm06CutInnerRoot data m i, hr⟩ v then 1 else 0) =
        gm06ComponentBits (gm06CutGraph n data) ⟨gm06CutInnerRoot data m i, hr⟩ from rfl,
      gm06CutBitVertices_eq, gm06CutInducedByVertices_component, gm06CutComponentAt_eq_some data hr]
  · simp only [gm06DecodeCutComponentBitsAt, hr, false_and, ↓reduceIte, gm06CutComponentAt, ↓reduceDIte]

/-- Decode consecutive bit rows using their cuff-gap indices. -/
def gm06DecodeCutComponentBitsFrom (n : ℕ) (data : GM06CutData) (m : ℕ) : ℕ → List (List ℕ) → List (Option GM06CutData)
  | _, [] => []
  | base, bits :: rows => gm06DecodeCutComponentBitsAt n data m base bits ::
      gm06DecodeCutComponentBitsFrom n data m (base + 1) rows

/-- Every decoded row gives its cuff-indexed finite component. -/
theorem gm06DecodeCutComponentBitsFrom_eq (n : ℕ) (data : GM06CutData) (m base k : ℕ) :
    gm06DecodeCutComponentBitsFrom n data m base (gm06CutComponentBitsFrom n data m base k) =
      (List.range' base k).map (fun i => gm06CutComponentAt n data (gm06CutInnerRoot data m i)) := by
  induction k generalizing base with
  | zero => simp [gm06CutComponentBitsFrom, gm06DecodeCutComponentBitsFrom]
  | succ k ih =>
    simp only [gm06CutComponentBitsFrom, gm06DecodeCutComponentBitsFrom,
      gm06DecodeCutComponentBitsAt_eq, ih, List.range'_succ, Nat.add_comm 1, List.map_cons]

end GraphMinor.Compute
