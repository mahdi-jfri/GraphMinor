module

public import GraphMinor.Compute.GM06CutMarkFacts

/-!
# Recovering linkage membership from the computed marks

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes
incoming and outgoing ends before duplicating a linkage edge. A nonzero table
entry must come from an actual path dart. Distinct incoming and
outgoing vertex keys ensure that each listed path end retains its
own mark. These facts identify the decoded local path ends with the
two orientations of the actual linkage darts.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A scatter lookup either retains the old lookup or comes from
one of its actual writes at that same index. -/
theorem gm06Scatter_getElem?_source (pairs : List (ℕ × ℕ)) (table : List ℕ) (v value : ℕ)
    (hv : v < table.length) (he : (gm06Scatter pairs table)[v]? = some value) :
    table[v]? = some value ∨ (v, value) ∈ pairs := by
  induction pairs generalizing table with
  | nil => exact Or.inl he
  | cons p pairs ih =>
    obtain h | h := ih (table.set p.1 p.2) (by simpa only [List.length_set] using hv) he
    · by_cases hp : p.1 = v
      · have hval : p.2 = value := by simpa only [hp, List.getElem?_set_self hv, Option.some.injEq] using h
        exact Or.inr (List.mem_cons.mpr (Or.inl (Prod.ext hp.symm hval.symm)))
      · exact Or.inl (by simpa only [List.getElem?_set_ne hp] using h)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A positive path-end mark is always an actual write, since the
initial table contains only zero. -/
theorem gm06Scatter_getElem?_positive_source (pairs : List (ℕ × ℕ)) (n v d : ℕ)
    (hv : v < n) (he : (gm06Scatter pairs (List.replicate n 0))[v]? = some (d + 1)) :
    (v, d + 1) ∈ pairs := by
  rcases gm06Scatter_getElem?_source pairs (List.replicate n 0) v (d + 1) (by simpa using hv) he with h | h
  · simp only [List.getElem?_replicate, hv, ↓reduceIte, Option.some.injEq] at h
    omega
  · exact h

/-- The decoded local path ends are precisely the nonzero incoming
and outgoing mark values, after removing the plus-one encoding. -/
theorem gm06CutPositionAt_pathEnds_iff (marks : GM06CutTables) (v d : ℕ) :
    (∃ p, gm06CutPositionAt marks v = some p ∧ d ∈ p.pathEnds) ↔
      marks.incoming[v]?.getD 0 = d + 1 ∨ marks.outgoing[v]?.getD 0 = d + 1 := by
  unfold gm06CutPositionAt
  dsimp only
  split_ifs <;> simp_all [GM06CutPosition.pathEnds] <;> omega

/-- A marked outgoing value identifies its actual directed path dart. -/
theorem gm06BuildCutTables_outgoing_source {n m v d : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ) (hv : v < n)
    (he : (gm06BuildCutTables n m origins paths inner outer).outgoing[v]?.getD 0 = d + 1) :
    d ∈ paths.flatten ∧ origins[d]?.getD 0 = v := by
  have hl : v < (gm06BuildCutTables n m origins paths inner outer).outgoing.length := by
    rw [(gm06BuildCutTables_lengths n m origins paths inner outer).2.1]
    exact hv
  have hlookup : (gm06BuildCutTables n m origins paths inner outer).outgoing[v]? = some (d + 1) := by
    rw [List.getElem?_eq_getElem hl] at he ⊢
    simpa only [Option.getD_some] using congrArg some he
  have hp := gm06Scatter_getElem?_positive_source
    (gm06CutPathEndPairs origins paths.flatten false) n v d hv hlookup
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  change (origins[q]?.getD 0, q + 1) = (v, d + 1) at heq
  have hlabel : q = d := by have h := congrArg Prod.snd heq; change q + 1 = d + 1 at h; omega
  subst q
  exact ⟨hq, congrArg Prod.fst heq⟩

/-- A marked incoming value identifies the reverse of an actual
arriving path dart. -/
theorem gm06BuildCutTables_incoming_source {n m v d : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ) (hv : v < n)
    (he : (gm06BuildCutTables n m origins paths inner outer).incoming[v]?.getD 0 = d + 1) :
    gm06DartMate d ∈ paths.flatten ∧ origins[d]?.getD 0 = v := by
  have hl : v < (gm06BuildCutTables n m origins paths inner outer).incoming.length := by
    rw [(gm06BuildCutTables_lengths n m origins paths inner outer).1]
    exact hv
  have hlookup : (gm06BuildCutTables n m origins paths inner outer).incoming[v]? = some (d + 1) := by
    rw [List.getElem?_eq_getElem hl] at he ⊢
    simpa only [Option.getD_some] using congrArg some he
  have hp := gm06Scatter_getElem?_positive_source
    (gm06CutPathEndPairs origins paths.flatten true) n v d hv hlookup
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hp
  change (origins[gm06DartMate q]?.getD 0, gm06DartMate q + 1) = (v, d + 1) at heq
  have hlabel : gm06DartMate q = d := by
    have h := congrArg Prod.snd heq
    change gm06DartMate q + 1 = d + 1 at h
    omega
  have hqeq : q = gm06DartMate d := by rw [← hlabel, gm06DartMate_involutive]
  exact ⟨hqeq ▸ hq, by simpa only [hlabel] using congrArg Prod.fst heq⟩

/-- Computed local path ends are exactly the two orientations of
linkage darts at their original origins. Unique end keys are the
finite vertex-disjoint simple-path condition on the linkage. -/
theorem gm06BuildCutTables_pathEnds_iff {n m d : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ) (hv : origins[d]?.getD 0 < n)
    (hin : ((gm06CutPathEndPairs origins paths.flatten true).map Prod.fst).Nodup)
    (hout : ((gm06CutPathEndPairs origins paths.flatten false).map Prod.fst).Nodup) :
    (∃ p, gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) (origins[d]?.getD 0) = some p ∧
      d ∈ p.pathEnds) ↔ d ∈ paths.flatten ∨ gm06DartMate d ∈ paths.flatten := by
  rw [gm06CutPositionAt_pathEnds_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr (gm06BuildCutTables_incoming_source origins paths inner outer hv h).1
    · exact Or.inl (gm06BuildCutTables_outgoing_source origins paths inner outer hv h).1
  · rintro (h | h)
    · have he := gm06BuildCutTables_outgoing_at (m := m) origins paths inner outer h hv hout
      exact Or.inr (by simp only [he, Option.getD_some])
    · have he := gm06BuildCutTables_incoming_at (m := m) (n := n) origins paths inner outer h
        (by simpa only [gm06DartMate_involutive d] using hv) hin
      exact Or.inl (by simpa only [gm06DartMate_involutive d, Option.getD_some] using congrArg (fun a => a.getD 0) he)

end GraphMinor.Compute
