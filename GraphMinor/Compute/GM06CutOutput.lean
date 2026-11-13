module

public import GraphMinor.Compute.GM06CutCuffMembershipProgram
public import GraphMinor.Compute.GM06CutMaterializeProgram

/-!
# Decoding the finite output of the linkage cut

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
cuff-indexed component graphs. The machine stores their vertex masks
and induced rotation records, together with the common origin table
and permanent active-label order. This file parses those records and
proves that they represent exactly the induced component data. The
decoder performs no reachability search or local side assignment.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Parse a specified number of complete component rotation records. -/
def gm06ReadComponentRotationsAux : ℕ → List ℕ → Option (List (List (List ℕ)) × List ℕ)
  | 0, words => some ([], words)
  | k + 1, words => do
      let (rows, rest) ← gm06ReadRows words
      let (components, tail) ← gm06ReadComponentRotationsAux k rest
      pure (rows :: components, tail)

/-- Every encoded component rotation record is parsed exactly. -/
theorem gm06ReadComponentRotationsAux_encode_append (components : List (List (List ℕ))) (tail : List ℕ) :
    gm06ReadComponentRotationsAux components.length (components.flatMap gm06EncodeRows ++ tail) =
      some (components, tail) := by
  induction components with
  | nil => rfl
  | cons rows components ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, gm06ReadComponentRotationsAux,
      gm06ReadRows_encode_append]
    change (do
      let (cs, rest) ← gm06ReadComponentRotationsAux components.length (components.flatMap gm06EncodeRows ++ tail)
      pure (rows :: cs, rest)) = _
    rw [ih]
    rfl

/-- A component list begins with its number of complete rotation records. -/
def gm06ReadComponentRotations : List ℕ → Option (List (List (List ℕ)) × List ℕ)
  | [] => none
  | k :: words => gm06ReadComponentRotationsAux k words

/-- Reconstruct graph data from explicit component vertices and rotations.
Active end labels retain their common permanent order. -/
def gm06DecodeCutComponentRecord (n : ℕ) (origins active bits : List ℕ) (rotations : List (List ℕ)) : GM06CutData :=
  { rotations := rotations
    origins := origins
    activeDarts := active.filter (fun d => decide (d ∈ rotations.flatten))
    vertices := gm06CutBitVertices n bits }

private theorem cutData_ext {a b : GM06CutData}
    (hr : a.rotations = b.rotations) (ho : a.origins = b.origins)
    (ha : a.activeDarts = b.activeDarts) (hv : a.vertices = b.vertices) : a = b := by
  cases a
  cases b
  cases hr
  cases ho
  cases ha
  cases hv
  rfl

/-- Explicit rotation records and vertex masks recover exactly the
induced finite graph. Every ambient active end must occur in its rotations. -/
theorem gm06DecodeCutComponentRecord_eq_induced (n : ℕ) (data : GM06CutData) (bits : List ℕ)
    (hcoverage : ∀ d ∈ data.activeDarts, d ∈ data.rotations.flatten) :
    gm06DecodeCutComponentRecord n data.origins data.activeDarts bits (gm06CutMaterializedRows n data bits) =
      gm06CutInducedByVertices data (gm06CutBitVertices n bits) := by
  have hrows : gm06CutMaterializedRows n data bits = (gm06CutInducedByVertices data (gm06CutBitVertices n bits)).rotations :=
    gm06CutComponentRotation_rows data _
  apply cutData_ext
  · exact hrows
  · rfl
  · unfold gm06DecodeCutComponentRecord
    rw [hrows]
    apply List.filter_congr
    intro d hd
    apply Bool.eq_iff_iff.mpr
    simp only [gm06CutInducedByVertices, ← List.filter_flatten, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hcoverage d hd, h⟩⟩
  · rfl

/-- The pure finite output of CUT_ALONG_LINKAGE, in inner cuff order. -/
def gm06CutAlongLinkage (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ) : List GM06CutData :=
  let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
  (gm06CutCuffMembership n m origins paths inner outer rows live).map
    (fun bits => gm06CutInducedByVertices data (gm06CutBitVertices (2 * n) bits))

/-- Parse the stored masks and physical rotation records into component data. -/
def gm06CutAlongLinkageResult (s : State) : Option (List GM06CutData) := do
  let (masks, _) ← gm06ReadRows (s.arrs 600)
  let (rotations, _) ← gm06ReadComponentRotations (gm06CutMaterializeResult s)
  if masks.length = rotations.length then
    pure ((masks.zip rotations).map (fun p => gm06DecodeCutComponentRecord
      (s.regs 620) (s.arrs 626) (s.arrs 628) p.1 p.2))
  else none

private theorem zip_materialized (n : ℕ) (data : GM06CutData) (masks : List (List ℕ))
    (hcoverage : ∀ d ∈ data.activeDarts, d ∈ data.rotations.flatten) :
    (masks.zip (masks.map (gm06CutMaterializedRows n data))).map
        (fun p => gm06DecodeCutComponentRecord n data.origins data.activeDarts p.1 p.2) =
      masks.map (fun bits => gm06CutInducedByVertices data (gm06CutBitVertices n bits)) := by
  induction masks with
  | nil => rfl
  | cons bits masks ih =>
    simp only [List.map_cons, List.zip_cons_cons, gm06DecodeCutComponentRecord_eq_induced n data bits hcoverage, ih]

/-- The physical mask and rotation outputs decode to the exact pure
induced component list, with no computed graph premise supplied. -/
theorem gm06CutAlongLinkageResult_eq {n : ℕ} (data : GM06CutData) (masks : List (List ℕ)) (s : State)
    (hcoverage : ∀ d ∈ data.activeDarts, d ∈ data.rotations.flatten)
    (h600 : s.arrs 600 = gm06EncodeRows masks)
    (hrotations : gm06CutMaterializeResult s = masks.length :: gm06CutMaterializedPayload n data masks)
    (h620 : s.regs 620 = n) (h626 : s.arrs 626 = data.origins) (h628 : s.arrs 628 = data.activeDarts) :
    gm06CutAlongLinkageResult s =
      some (masks.map (fun bits => gm06CutInducedByVertices data (gm06CutBitVertices n bits))) := by
  have hm := gm06ReadRows_encode_append masks []
  simp only [List.append_nil] at hm
  have hr := gm06ReadComponentRotationsAux_encode_append (masks.map (gm06CutMaterializedRows n data)) []
  simp only [List.length_map, List.flatMap_map, List.append_nil, Function.comp_def] at hr
  simp only [gm06CutAlongLinkageResult, h600, hm, hrotations, gm06ReadComponentRotations,
    gm06CutMaterializedPayload, hr, Option.bind_some, List.length_map, ↓reduceIte, h620, h626, h628]
  change (if masks.length = (masks.map (gm06CutMaterializedRows n data)).length then
    some ((masks.zip (masks.map (gm06CutMaterializedRows n data))).map
      (fun p => gm06DecodeCutComponentRecord n data.origins data.activeDarts p.1 p.2)) else none) = _
  simp only [List.length_map, ↓reduceIte]
  exact congrArg some (zip_materialized n data masks hcoverage)

/-- At a valid cuff root, the interpreted mask is its exact component. -/
theorem gm06CutInducedByVertices_bitsAt {n m i : ℕ} (data : GM06CutData)
    (hr : gm06CutInnerRoot data m i < n) :
    some (gm06CutInducedByVertices data (gm06CutBitVertices n (gm06CutComponentBitsAt n data m i))) =
      gm06CutComponentAt n data (gm06CutInnerRoot data m i) := by
  rw [gm06CutComponentBitsAt_eq data hr, gm06CutBitVertices_eq, gm06CutInducedByVertices_component,
    gm06CutComponentAt_eq_some data hr]

/-- Consecutive valid cuff masks describe exactly the cuff-indexed components. -/
theorem gm06CutInducedByVertices_bitsFrom (n : ℕ) (data : GM06CutData) (m base k : ℕ)
    (hroots : ∀ i, base ≤ i → i < base + k → gm06CutInnerRoot data m i < n) :
    (gm06CutComponentBitsFrom n data m base k).map
        (fun bits => some (gm06CutInducedByVertices data (gm06CutBitVertices n bits))) =
      (List.range' base k).map (fun i => gm06CutComponentAt n data (gm06CutInnerRoot data m i)) := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    simp only [gm06CutComponentBitsFrom, List.map_cons, List.range'_succ,
      gm06CutInducedByVertices_bitsAt data (hroots base le_rfl (by omega))]
    rw [ih (base + 1) (fun i hlo hhi => hroots i (by omega) (by omega))]

end GraphMinor.Compute
