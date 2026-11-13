module

public import GraphMinor.Compute.GM06Reduction4Finite

/-!
# Deterministic Reduction 4 candidate search

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) tries
contacts in increasing path position and accepts the first successful BFS.
This file gives that finite search for one cut component. The
candidate graphs and increasing neighbour lists are computed from
the component's edge and incidence lists. Failure means that every
eligible contact is unreachable in its exact candidate graph.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Try a finite list of searches, retaining the first successful index. -/
def gm06FirstSuccessful {α : Type*} (search : ℕ → Option α) : List ℕ → Option (ℕ × α)
  | [] => none
  | j :: js => match search j with
    | some path => some (j, path)
    | none => gm06FirstSuccessful search js

/-- A failed first-success scan means every attempted search failed. -/
theorem gm06FirstSuccessful_none_iff {α : Type*} (search : ℕ → Option α) (js : List ℕ) :
    gm06FirstSuccessful search js = none ↔ ∀ j ∈ js, search j = none := by
  induction js with
  | nil => simp [gm06FirstSuccessful]
  | cons j js ih =>
    cases h : search j with
    | none => simp [gm06FirstSuccessful, h, ih]
    | some path => simp [gm06FirstSuccessful, h]

/-- The returned index was inspected, and its search returned exactly
the reported value. No failed candidate is treated as a witness. -/
theorem gm06FirstSuccessful_sound {α : Type*} (search : ℕ → Option α) (js : List ℕ)
    (j : ℕ) (path : α) (h : gm06FirstSuccessful search js = some (j, path)) :
    j ∈ js ∧ search j = some path := by
  induction js with
  | nil => cases h
  | cons i js ih =>
    cases hi : search i with
    | none =>
      have h' : gm06FirstSuccessful search js = some (j, path) := by
        simpa only [gm06FirstSuccessful, hi] using h
      obtain ⟨hj, hp⟩ := ih h'
      exact ⟨List.mem_cons_of_mem i hj, hp⟩
    | some p =>
      have heq : (i, p) = (j, path) := by simpa only [gm06FirstSuccessful, hi, Option.some.injEq] using h
      cases heq
      exact ⟨List.mem_cons_self, hi⟩

/-- The path vertex list in permanent cut-vertex labels. -/
def gm06Find4PathVertices {n : ℕ} (start : Fin n) (steps : List (ℕ × Fin n)) : List ℕ :=
  start.val :: steps.map (fun step => step.2.val)

/-- The arrival vertex at a candidate position. Valid contact positions
are positive and at most the step-list length. -/
def gm06Find4Target {n : ℕ} (start : Fin n) (steps : List (ℕ × Fin n)) (j : ℕ) : Fin n :=
  ((steps[j - 1]?).map Prod.snd).getD start

/-- The exact candidate graph for a single contact. -/
def gm06Find4Graph {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) (j : ℕ) :
    SimpleGraph (Fin n) :=
  gm06CandidateGraph n ends ordinary incV incE upper (gm06Find4PathVertices start steps) j

instance gm06Find4Graph_decidableRel {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) (j : ℕ) :
    DecidableRel (gm06Find4Graph ends ordinary incV incE upper start steps j).Adj :=
  gm06CandidateGraph_decidableRel _ _ _ _ _ _ _ _

/-- An actual BFS attempt, rather than an incidence-only test. -/
def gm06Find4Attempt {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) (j : ℕ) :
    Option (List ℕ) :=
  let G := gm06Find4Graph ends ordinary incV incE upper start steps j
  gm06BfsPathWords G (gm06OrderedNeighbours G) start (gm06Find4Target start steps j)

/-- Pure FIND_4 for one component. Incidence chooses contacts, then
BFS tests each corresponding graph, in increasing contact order. -/
def gm06Find4 {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) :
    Option (ℕ × List ℕ) :=
  gm06FirstSuccessful (gm06Find4Attempt ends ordinary incV incE upper start steps)
    (gm06Reduction4Contacts incV incE start.val (steps.map (fun step => (step.1, step.2.val))))

/-- Every returned value is the vertex list of a simple path in the
exact candidate graph at the returned contact. -/
theorem gm06Find4_sound {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n))
    (j : ℕ) (path : List ℕ) (h : gm06Find4 ends ordinary incV incE upper start steps = some (j, path)) :
    j ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun step => (step.1, step.2.val))) ∧
    ∃ p : (gm06Find4Graph ends ordinary incV incE upper start steps j).Walk
        start (gm06Find4Target start steps j), p.IsPath ∧ p.support.map Fin.val = path := by
  obtain ⟨hj, hp⟩ := gm06FirstSuccessful_sound _ _ j path h
  refine ⟨hj, ?_⟩
  obtain ⟨p, hsome, hwords⟩ := Option.map_eq_some_iff.mp hp
  refine ⟨p, gm06BfsPath_isPath _ _ (gm06OrderedNeighbours_spec _) _ _ p hsome, hwords⟩

/-- FIND_4 fails exactly when every eligible contact is unreachable
in its corresponding graph. This is a finite statement and assumes
no geometric reduction-existence theorem. -/
theorem gm06Find4_none_iff {n : ℕ} (ends : List (ℕ × ℕ)) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) :
    gm06Find4 ends ordinary incV incE upper start steps = none ↔
      ∀ j ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun step => (step.1, step.2.val))),
        ¬ (gm06Find4Graph ends ordinary incV incE upper start steps j).Reachable
          start (gm06Find4Target start steps j) := by
  rw [gm06Find4, gm06FirstSuccessful_none_iff]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  change Option.map _ (gm06BfsPath _ _ _ _) = none ↔ _
  rw [Option.map_eq_none_iff]
  exact gm06BfsPath_none_iff _ _ (gm06OrderedNeighbours_spec _) _ _

end GraphMinor.Compute
