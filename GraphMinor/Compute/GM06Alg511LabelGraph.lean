module

public import GraphMinor.Surface.Defs
public import GraphMinor.Compute.GM06Alg511TurnWords
import Mathlib.Tactic

/-!
# The finite edge-labelled graph of a cylinder input

Keep each supplied edge position, including loops and parallel edges.
A walk in this finite graph records the vertex and edge labels used
by the winding computation of VI (5.11), page 134. Orient a dart by
comparing its start with the edge's first endpoint. The resulting
finite dart list has exactly the turn sum computed by the verified
RAM accumulator. This graph stores no embedding, linkage or answer.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface Set

/-- A finite graph with one separately labelled edge per supplied
endpoint pair. Every supplied vertex label is retained. -/
def gm06Alg511LabelGraph {n : ℕ} (pairs : List (Fin n × Fin n)) :
    Graph (Fin n) (Fin pairs.length) where
  vertexSet := univ
  edgeSet := univ
  IsLink e a b := (a = pairs[e.val].1 ∧ b = pairs[e.val].2) ∨
    (a = pairs[e.val].2 ∧ b = pairs[e.val].1)
  isLink_symm _ _ := ⟨fun _ _ h => h.elim
    (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b c d h₁ h₂
    rcases h₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rcases h₂ with ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Or.inl (ha.trans hc.symm)
    · exact Or.inr (ha.trans hd.symm)
    · exact Or.inr (ha.trans hd.symm)
    · exact Or.inl (ha.trans hc.symm)
  edge_mem_iff_exists_isLink e :=
    ⟨fun _ => ⟨pairs[e.val].1, pairs[e.val].2, Or.inl ⟨rfl, rfl⟩⟩, fun _ => trivial⟩
  left_mem_of_isLink := by intro e a b h; trivial

/-- The signed turn of one finite oriented edge traversal. -/
def gm06Alg511LabelEdgeTurn {n : ℕ} (pairs : List (Fin n × Fin n)) (turns : List ℤ)
    {e : Fin pairs.length} {a b : Fin n} (_ : (gm06Alg511LabelGraph pairs).IsLink e a b) : ℤ :=
  if a = pairs[e.val].1 then turns.getD e.val 0 else -turns.getD e.val 0

/-- The dart position of one finite oriented edge traversal. -/
def gm06Alg511LabelDart {n : ℕ} (pairs : List (Fin n × Fin n))
    {e : Fin pairs.length} {a b : Fin n} (_ : (gm06Alg511LabelGraph pairs).IsLink e a b) : ℕ :=
  2 * e.val + if a = pairs[e.val].1 then 0 else 1

/-- Sum the supplied integer turns along a finite edge-labelled walk. -/
def gm06Alg511LabelWalkTurn {n : ℕ} (pairs : List (Fin n × Fin n)) (turns : List ℤ) :
    ∀ {a b : Fin n}, GraphWalk (gm06Alg511LabelGraph pairs) a b → ℤ
  | _, _, .nil _ => 0
  | _, _, .cons he W => gm06Alg511LabelEdgeTurn pairs turns he + gm06Alg511LabelWalkTurn pairs turns W

/-- Read the oriented edge positions of a finite walk. -/
def gm06Alg511LabelWalkDarts {n : ℕ} (pairs : List (Fin n × Fin n)) :
    ∀ {a b : Fin n}, GraphWalk (gm06Alg511LabelGraph pairs) a b → List ℕ
  | _, _, .nil _ => []
  | _, _, .cons he W => gm06Alg511LabelDart pairs he :: gm06Alg511LabelWalkDarts pairs W

/-- Every recorded dart is a valid position in the signed-turn words. -/
theorem gm06Alg511LabelWalkDarts_lt {n : ℕ} (pairs : List (Fin n × Fin n))
    {a b : Fin n} (W : GraphWalk (gm06Alg511LabelGraph pairs) a b) :
    ∀ d ∈ gm06Alg511LabelWalkDarts pairs W, d < 2 * pairs.length := by
  induction W with
  | nil _ => simp [gm06Alg511LabelWalkDarts]
  | @cons a c b e he W ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · unfold gm06Alg511LabelDart
      split <;> omega
    · exact ih d hd

/-- The finite walk turn sum is exactly the signed sum read by the
RAM accumulator on its dart list. -/
theorem gm06Alg511LabelWalkTurn_eq_dartSum {n : ℕ}
    (pairs : List (Fin n × Fin n)) (turns : List ℤ) (hlen : turns.length = pairs.length)
    {a b : Fin n} (W : GraphWalk (gm06Alg511LabelGraph pairs) a b) :
    gm06Alg511LabelWalkTurn pairs turns W =
      ((gm06Alg511LabelWalkDarts pairs W).map
        (gm06Alg511DartTurn (gm06Alg511TurnWords turns))).sum := by
  induction W with
  | nil _ => rfl
  | @cons a c b e he W ih =>
    change gm06Alg511LabelEdgeTurn pairs turns he + gm06Alg511LabelWalkTurn pairs turns W = _
    rw [ih]
    change _ = gm06Alg511DartTurn (gm06Alg511TurnWords turns) (gm06Alg511LabelDart pairs he) + _
    congr 1
    have hi : e.val < turns.length := by rw [hlen]; exact e.isLt
    by_cases ha : a = pairs[e.val].1
    · simp only [gm06Alg511LabelEdgeTurn, gm06Alg511LabelDart, ha, ite_true, Nat.add_zero]
      exact (gm06Alg511DartTurn_forward turns e.val hi).symm
    · simp only [gm06Alg511LabelEdgeTurn, gm06Alg511LabelDart, ha, ite_false]
      exact (gm06Alg511DartTurn_reverse turns e.val hi).symm

end GraphMinor.Compute
