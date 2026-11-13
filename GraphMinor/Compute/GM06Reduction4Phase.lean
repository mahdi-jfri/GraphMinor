module

public import GraphMinor.Compute.GM06SuccessorInput
public import GraphMinor.Compute.GM06CutOutput
public import GraphMinor.Compute.GM06CutFaceInput
public import GraphMinor.Compute.GM06CandidateInput
public import GraphMinor.Compute.GM06Find4DartsProgram
public import GraphMinor.Compute.GM06Apply4Program

/-!
# The finite Reduction 4 phase

Sections 9, 10, 12 and 13 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) cut the current rotations, select each reverse-inner-cuff
face and search its candidate graphs in cuff order. The first successful
search replaces exactly its original linkage row. These functions
compose the finite list operations, without reading any geometric
answer or precomputed incidence. Retired vertex slots remain in the
permanent label space and have empty rotations.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- All cuff-indexed components of the current finite drawing. -/
def gm06PhaseComponents (x : GM06SuccessorInput) (m : ℕ) : List GM06CutData :=
  gm06CutAlongLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount)

/-- The next boundary index, retaining the other copy when there is
only one original path. -/
def gm06PhaseNext (x : GM06SuccessorInput) (i : ℕ) : ℕ := (i + 1) % x.innerCuff.length

/-- Original directed path heads, in a chosen permanent copy slot. -/
def gm06PhaseBoundaryVertices (x : GM06SuccessorInput) (i tag : ℕ) : List ℕ :=
  (2 * x.innerCuff[i]?.getD 0 + tag) ::
    (x.linkage[i]?.getD []).map (fun d => 2 * x.endpoints[gm06DartMate d]?.getD 0 + tag)

/-- Left copied path edges and arrival vertices, retaining the actual
ordinary edge labels even when distinct edges have equal endpoints. -/
def gm06PhaseLeftSteps (x : GM06SuccessorInput) (i : ℕ) : List (ℕ × ℕ) :=
  (x.linkage[i]?.getD []).map (fun d =>
    (2 * (d / 2), 2 * x.endpoints[gm06DartMate d]?.getD 0))

/-- Convert numeric arrival labels into finite labels. The remainder
only makes the function total on malformed input; valid labels are
unchanged, as proved below. -/
def gm06PhaseFinSteps (n : ℕ) (hn : 0 < n) (steps : List (ℕ × ℕ)) : List (ℕ × Fin n) :=
  steps.map (fun p => (p.1, ⟨p.2 % n, Nat.mod_lt _ hn⟩))

/-- Numeric-input wrapper for the already verified directed FIND_4.
The empty permanent vertex space cannot contain a source. -/
def gm06PhaseFind4Words (n m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper : List ℕ) (source : ℕ) (steps : List (ℕ × ℕ)) : Option (ℕ × List ℕ) :=
  if hn : 0 < n then
    gm06Find4Darts m origins ordinary incV incE upper
      ⟨source % n, Nat.mod_lt _ hn⟩ (gm06PhaseFinSteps n hn steps)
  else none

/-- On valid numeric labels, the finite-label wrapper is precisely the
same directed FIND_4, with every supplied source and arrival unchanged. -/
theorem gm06PhaseFind4Words_eq {n m : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper : List ℕ) (source : Fin n) (steps : List (ℕ × Fin n)) :
    gm06PhaseFind4Words n m origins ordinary incV incE upper source.val
      (steps.map (fun p => (p.1, p.2.val))) =
      gm06Find4Darts m origins ordinary incV incE upper source steps := by
  have hn : 0 < n := Nat.zero_lt_of_lt source.isLt
  have hsource : (⟨source.val % n, Nat.mod_lt _ hn⟩ : Fin n) = source :=
    Fin.ext (Nat.mod_eq_of_lt source.isLt)
  have hsteps : gm06PhaseFinSteps n hn (steps.map (fun p => (p.1, p.2.val))) = steps := by
    unfold gm06PhaseFinSteps
    rw [List.map_map]
    conv_rhs => rw [← List.map_id steps]
    apply List.map_congr_left
    intro p _
    exact Prod.ext rfl (Fin.ext (Nat.mod_eq_of_lt p.2.isLt))
  simp only [gm06PhaseFind4Words, hn, ↓reduceDIte, hsource, hsteps]

/-- The numeric path row supplied to FIND_4 is exactly the left
boundary vertex list of the actual original path. -/
theorem gm06PhaseLeftSteps_vertices (x : GM06SuccessorInput) (i : ℕ) :
    (2 * x.innerCuff[i]?.getD 0) :: (gm06PhaseLeftSteps x i).map Prod.snd =
      gm06PhaseBoundaryVertices x i 0 := by
  simp only [gm06PhaseLeftSteps, gm06PhaseBoundaryVertices, List.map_map, Function.comp_def, Nat.add_zero]

/-- Incidence and directed search for one computed component. -/
def gm06Reduction4PhaseComponent (x : GM06SuccessorInput) (m i : ℕ) (part : GM06CutData) :
    Option (ℕ × List ℕ) := do
  let (_, incV, incE) ← gm06CutFaceIncidence (2 * x.vertexCount)
    (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1)
  gm06PhaseFind4Words (2 * x.vertexCount) (2 * (m + x.innerCuff.length + x.outerCuff.length))
    part.origins (gm06CandidateOrdinary (2 * (m + x.innerCuff.length + x.outerCuff.length)) m)
    incV incE (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1)
    (2 * x.innerCuff[i]?.getD 0) (gm06PhaseLeftSteps x i)

/-- An out-of-range component contributes no witness. -/
def gm06Reduction4PhaseAt (x : GM06SuccessorInput) (m i : ℕ) : Option (ℕ × List ℕ) :=
  ((gm06PhaseComponents x m)[i]?).bind (gm06Reduction4PhaseComponent x m i)

/-- Inspect components in the order of their original inner cuff gaps. -/
def gm06Reduction4PhaseWitness (x : GM06SuccessorInput) (m : ℕ) : Option (ℕ × ℕ × List ℕ) :=
  gm06FirstSuccessful (gm06Reduction4PhaseAt x m) (List.range x.innerCuff.length)

/-- Exact bit and full linkage output of the Reduction 4 phase. -/
def gm06Reduction4Phase (x : GM06SuccessorInput) (m : ℕ) : Bool × List (List ℕ) :=
  match gm06Reduction4PhaseWitness x m with
  | none => (false, x.linkage)
  | some (i, j, darts) => (true, gm06Apply4Paths darts x.linkage i j)

/-- The whole phase fails exactly when every component search fails. -/
theorem gm06Reduction4PhaseWitness_none_iff (x : GM06SuccessorInput) (m : ℕ) :
    gm06Reduction4PhaseWitness x m = none ↔
      ∀ i < x.innerCuff.length, gm06Reduction4PhaseAt x m i = none := by
  simp only [gm06Reduction4PhaseWitness, gm06FirstSuccessful_none_iff, List.mem_range]

/-- A reported phase witness is the exact output of its indexed
component search. -/
theorem gm06Reduction4PhaseWitness_some {x : GM06SuccessorInput} {m i j : ℕ} {darts : List ℕ}
    (h : gm06Reduction4PhaseWitness x m = some (i, j, darts)) :
    i < x.innerCuff.length ∧ gm06Reduction4PhaseAt x m i = some (j, darts) := by
  have hh := gm06FirstSuccessful_sound (gm06Reduction4PhaseAt x m)
    (List.range x.innerCuff.length) i (j, darts) h
  exact ⟨List.mem_range.mp hh.1, hh.2⟩

/-- Failure leaves the complete linkage unchanged. -/
theorem gm06Reduction4Phase_of_none {x : GM06SuccessorInput} {m : ℕ}
    (h : gm06Reduction4PhaseWitness x m = none) : gm06Reduction4Phase x m = (false, x.linkage) := by
  simp only [gm06Reduction4Phase, h]

/-- Success is exactly the old pure APPLY_4 operation at its returned
contact, including projection of the actual copied directed darts. -/
theorem gm06Reduction4Phase_of_some {x : GM06SuccessorInput} {m i j : ℕ} {darts : List ℕ}
    (h : gm06Reduction4PhaseWitness x m = some (i, j, darts)) :
    gm06Reduction4Phase x m = (true, gm06Apply4Paths darts x.linkage i j) := by
  simp only [gm06Reduction4Phase, h]

end GraphMinor.Compute
