module

public import GraphMinor.Compute.GM06FaceIncidence
public import GraphMinor.Compute.GM06BfsPath

/-!
# The finite tests for Reduction 4

Sections 12--13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) remove
the opposite boundary and the retained suffix before searching. Only
ordinary edges incident with the selected face can be used. This
file states that candidate graph directly from lists and proves the
prefix invariant (11). Candidate contacts are scanned in path order;
incidence with the contact alone never certifies a reduction.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a dense incidence bit as a Boolean. Missing labels are absent. -/
def gm06Incident (bits : List ℕ) (v : ℕ) : Bool := bits[v]?.getD 0 != 0

/-- One path step is represented by its edge and its arrival vertex. -/
def gm06PrefixStepOK (incV incE : List ℕ) (step : ℕ × ℕ) : Bool :=
  gm06Incident incE step.1 && gm06Incident incV step.2

/-- The prefix flag updated once for each edge and arrival vertex. -/
def gm06PrefixOK (incV incE : List ℕ) (start : ℕ) (steps : List (ℕ × ℕ)) : Bool :=
  steps.foldl (fun ok step => ok && gm06PrefixStepOK incV incE step) (gm06Incident incV start)

private theorem and_fold {α : Type*} (check : α → Bool) (xs : List α) (b : Bool) :
    xs.foldl (fun ok x => ok && check x) b = (b && xs.all check) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]

/-- Equation (11): the running flag holds exactly when every vertex
and edge of the processed prefix is incident with the selected face. -/
theorem gm06PrefixOK_iff (incV incE : List ℕ) (start : ℕ)
    (steps : List (ℕ × ℕ)) (j : ℕ) :
    gm06PrefixOK incV incE start (steps.take j) = true ↔
      incV[start]?.getD 0 ≠ 0 ∧
      ∀ step ∈ steps.take j, incE[step.1]?.getD 0 ≠ 0 ∧ incV[step.2]?.getD 0 ≠ 0 := by
  simp [gm06PrefixOK, and_fold, gm06PrefixStepOK, gm06Incident]

/-- The next update is exactly the conjunction in FIND_4. -/
theorem gm06PrefixOK_append_one (incV incE : List ℕ) (start : ℕ)
    (steps : List (ℕ × ℕ)) (step : ℕ × ℕ) :
    gm06PrefixOK incV incE start (steps ++ [step]) =
      ((gm06PrefixOK incV incE start steps && gm06Incident incE step.1) &&
        gm06Incident incV step.2) := by
  simp only [gm06PrefixOK, List.foldl_append, List.foldl_cons, List.foldl_nil,
    gm06PrefixStepOK, Bool.and_assoc]

/-- The vertices of the candidate graph: selected-face incidence,
excluding every opposite-boundary vertex and the strictly retained tail. -/
def gm06CandidateVertex (incV upper path : List ℕ) (j v : ℕ) : Bool :=
  gm06Incident incV v && !upper.contains v && !(path.drop (j + 1)).contains v

/-- The exact retained-vertex criterion of Section 12. -/
theorem gm06CandidateVertex_iff (incV upper path : List ℕ) (j v : ℕ) :
    gm06CandidateVertex incV upper path j v = true ↔
      incV[v]?.getD 0 ≠ 0 ∧ v ∉ upper ∧ v ∉ path.drop (j + 1) := by
  simp [gm06CandidateVertex, gm06Incident, and_assoc]

/-- Candidate edge labels, in increasing input-edge order. The
ordinary flag is false for every auxiliary cuff edge. -/
def gm06CandidateEdges (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) : List ℕ :=
  (List.range ends.length).filter (fun e => ordinary[e]?.getD false &&
    gm06Incident incE e &&
    gm06CandidateVertex incV upper path j (ends[e]?.getD (0, 0)).1 &&
    gm06CandidateVertex incV upper path j (ends[e]?.getD (0, 0)).2)

/-- The graph has precisely the ordinary, incident edges whose two
ends remain. In particular no cuff edge can occur in a search path. -/
theorem gm06CandidateEdges_mem_iff (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j e : ℕ) :
    e ∈ gm06CandidateEdges ends ordinary incV incE upper path j ↔
      e < ends.length ∧ ordinary[e]?.getD false = true ∧ incE[e]?.getD 0 ≠ 0 ∧
      gm06CandidateVertex incV upper path j (ends[e]?.getD (0, 0)).1 = true ∧
      gm06CandidateVertex incV upper path j (ends[e]?.getD (0, 0)).2 = true := by
  simp [gm06CandidateEdges, gm06Incident, and_assoc]

/-- Underlying simple graph of the retained finite edges. Loops
have no role in a simple source path. Edge labels are kept in the
separate candidate-edge list, including parallel edges. -/
def gm06CandidateGraph (n : ℕ) (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ e ∈ gm06CandidateEdges ends ordinary incV incE upper path j,
    (ends[e]?.getD (0, 0) = (u.val, v.val) ∨ ends[e]?.getD (0, 0) = (v.val, u.val))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp (fun _ he => ⟨he.1, he.2.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Candidate adjacency is a finite search over the retained edge list. -/
instance gm06CandidateGraph_decidableRel (n : ℕ) (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) :
    DecidableRel (gm06CandidateGraph n ends ordinary incV incE upper path j).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ ∃ e ∈
    gm06CandidateEdges ends ordinary incV incE upper path j, _))

/-- Increasing neighbour lists, computed directly from decidable adjacency. -/
def gm06OrderedNeighbours {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : List ℕ :=
  ((List.finRange n).filter (fun v => decide (G.Adj u v))).map Fin.val

/-- The computed increasing lists represent their graph exactly. -/
theorem gm06OrderedNeighbours_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    IsAdjListFamily G (gm06OrderedNeighbours G) := by
  intro u
  have hn : (((List.finRange n).filter (fun v => decide (G.Adj u v))).map Fin.val).Nodup :=
    ((List.nodup_finRange n).filter _).map Fin.val_injective
  refine ⟨?_, hn, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact v.isLt
  · simp only [gm06OrderedNeighbours, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  · intro v
    simp only [gm06OrderedNeighbours, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, hv⟩
      exact (Fin.ext hv) ▸ ha
    · intro h
      exact ⟨v, h, rfl⟩

/-- The list of contacts that pass the incidence and violating-prefix
tests. Position zero is excluded. Each contact still requires BFS. -/
def gm06Reduction4Contacts (incV incE : List ℕ) (start : ℕ)
    (steps : List (ℕ × ℕ)) : List ℕ :=
  ((List.range steps.length).filter (fun q =>
    gm06Incident incV (steps[q]?.getD (0, 0)).2 &&
      !gm06PrefixOK incV incE start (steps.take (q + 1)))).map (· + 1)

/-- APPLY_4's replacement dart row, before the outer driver installs
it in the selected linkage row and invalidates its caches. -/
def gm06Apply4Row (project : ℕ → ℕ) (replacement oldPath : List ℕ) (j : ℕ) : List ℕ :=
  replacement.map project ++ oldPath.drop j

/-- Copying a prefix of the replacement gives exactly the same
prefix of the completed Reduction 4 row. -/
theorem gm06Apply4Row_prefix (project : ℕ → ℕ) (replacement oldPath : List ℕ)
    (j q : ℕ) (hq : q ≤ replacement.length) :
    (gm06Apply4Row project replacement oldPath j).take q = (replacement.take q).map project := by
  simp only [gm06Apply4Row, List.take_append, List.length_map, Nat.sub_eq_zero_of_le hq,
    List.take_zero, List.append_nil, List.map_take]

end GraphMinor.Compute
