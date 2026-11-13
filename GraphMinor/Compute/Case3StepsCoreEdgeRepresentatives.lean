module

public import GraphMinor.Compute.Case3StepsFirstIndex
public import GraphMinor.Compute.Case3StepsParseProg

/-!
# Labels for the core-edge raw members

A core edge joins a component group when its pair of boundary vertices
matches that group's attachments. Otherwise it is a separate raw member.
The separate labels start after all vertex labels, so they cannot collide
with component representatives. This implements type (i) and its merging
rule in the description of XIII (8.6), page 96.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Reuse a component boundary representative, or retain the edge's own label. -/
noncomputable def case3CoreEdgeRepresentative (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (j : ℕ) : ℕ :=
  let r := case3FirstIndex (fun z => z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v})
  if r < x.n then r else x.n + j

/-- The label entry of one canonical simple edge. -/
noncomputable def case3CoreEdgeRepEntry (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) : ℕ :=
  let e := (case3InputEdges x)[j.1]
  if e.1 ∈ Z ∧ e.2 ∈ Z then case3CoreEdgeRepresentative x Z e.1 e.2 j.1
  else x.n + (case3InputEdges x).length

/-- Core-edge labels, with `n + m` as the sentinel for non-core edges. -/
noncomputable def case3CoreEdgeRepList (x : Alg81Input) (Z : Finset (Fin x.n)) : List ℕ :=
  List.ofFn (case3CoreEdgeRepEntry x Z)

/-- There is one word per simple edge. -/
theorem case3CoreEdgeRepList_length (x : Alg81Input) (Z : Finset (Fin x.n)) :
    (case3CoreEdgeRepList x Z).length = (case3InputEdges x).length := by
  simp only [case3CoreEdgeRepList, List.length_ofFn]

/-- Every genuine core-edge label lies below the common missing sentinel. -/
theorem case3CoreEdgeRepresentative_lt {m : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (j : ℕ) (hj : j < m) :
    case3CoreEdgeRepresentative x Z u v j < x.n + m := by
  unfold case3CoreEdgeRepresentative
  dsimp only
  split_ifs with h
  · omega
  · omega

/-- Every edge-table word is at most the common missing sentinel. -/
theorem case3CoreEdgeRepEntry_le (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) :
    case3CoreEdgeRepEntry x Z j ≤ x.n + (case3InputEdges x).length := by
  unfold case3CoreEdgeRepEntry
  dsimp only
  split_ifs
  · exact (case3CoreEdgeRepresentative_lt x Z _ _ j.1 j.2).le
  · rfl

/-- A separate core-edge label occurs exactly when no component has its
boundary pair as attachment set. -/
theorem case3CoreEdgeRepresentative_eq_own_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (j : ℕ) :
    case3CoreEdgeRepresentative x Z u v j = x.n + j ↔
      ∀ z : Fin x.n, ¬ (z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v}) := by
  let P := fun z : Fin x.n => z ∉ Z ∧ case3AttachmentRowSet x Z z = {u, v}
  have hle := case3FirstIndex_le P
  change (if case3FirstIndex P < x.n then case3FirstIndex P else x.n + j) = x.n + j ↔ _
  by_cases hlt : case3FirstIndex P < x.n
  · simp only [hlt, ↓reduceIte]
    constructor
    · intro heq
      omega
    · intro hnone
      have heq := (case3FirstIndex_eq_sentinel_iff P).mpr hnone
      omega
  · have heq : case3FirstIndex P = x.n := by omega
    simp only [hlt, ↓reduceIte, true_iff]
    exact (case3FirstIndex_eq_sentinel_iff P).mp heq

/-- A core-edge candidate is selected exactly when its label is its own
index. This also ensures that both endpoints are in the core. -/
theorem case3CoreEdgeRepEntry_eq_own_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) :
    case3CoreEdgeRepEntry x Z j = x.n + j.1 ↔
      (let e := (case3InputEdges x)[j.1]
       (e.1 ∈ Z ∧ e.2 ∈ Z) ∧
         ∀ z : Fin x.n, ¬ (z ∉ Z ∧ case3AttachmentRowSet x Z z = {e.1, e.2})) := by
  unfold case3CoreEdgeRepEntry
  dsimp only
  by_cases hc : ((case3InputEdges x)[j.1]).1 ∈ Z ∧ ((case3InputEdges x)[j.1]).2 ∈ Z
  · simp only [hc, true_and]
    exact case3CoreEdgeRepresentative_eq_own_iff x Z _ _ j.1
  · simp only [hc, ↓reduceIte, false_and, iff_false]
    have hj := j.2
    omega

end GraphMinor.Compute
