module

public import GraphMinor.Compute.Case3StepsEdgeMatrix
import GraphMinor.Compute.Case3StepsReadCoreEdgeProg
import GraphMinor.Compute.Case3StepsPairKey
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Set.Insert

/-!
# Looking up owners in the endpoint table

Different canonical simple edges have different unordered endpoint pairs.
Thus each edge's two matrix entries receive its label exactly once. The
completed matrix consequently tests exact selected-member membership for
either direction of every simple edge.
-/

public section

namespace GraphMinor.Compute

/-- Row-major endpoint positions identify both endpoints. -/
theorem case3PairPosition_injective {n : ℕ} (u v a b : Fin n)
    (h : case3PairPosition u v = case3PairPosition a b) : u = a ∧ v = b := by
  have hp : finProdFinEquiv (u, v) = finProdFinEquiv (a, b) := by
    apply Fin.ext
    change v.1 + n * u.1 = b.1 + n * a.1
    simpa only [case3PairPosition, Nat.add_comm, Nat.mul_comm] using h
  exact Prod.mk.inj (finProdFinEquiv.injective hp)

private theorem pair_orientations {n : ℕ} (u v a b : Fin n)
    (h : ({u, v} : Finset (Fin n)) = {a, b}) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hs := congrArg (fun S : Finset (Fin n) => (S : Set (Fin n))) h
  simp only [Finset.coe_insert, Finset.coe_singleton] at hs
  exact Set.pair_eq_pair_iff.mp hs

private theorem canonical_edge_eq_of_pair (x : Alg81Input)
    (j k : Fin (case3InputEdges x).length)
    (h : ({((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2} : Finset (Fin x.n)) =
      {((case3InputEdges x)[k.1]).1, ((case3InputEdges x)[k.1]).2}) : j = k := by
  have hj := (case3InputEdges_get_spec x j).1
  have hk := (case3InputEdges_get_spec x k).1
  have he : (case3InputEdges x)[j.1] = (case3InputEdges x)[k.1] := by
    rcases pair_orientations _ _ _ _ h with h | h
    · exact Prod.ext h.1 h.2
    · rw [h.1, h.2] at hj
      exact False.elim (lt_asymm hj hk)
  exact Fin.ext ((nodup_edgeListOf x.G).getElem_inj.mp he)

private theorem target_collision (x : Alg81Input)
    (j k : Fin (case3InputEdges x).length) (u v : Fin x.n)
    (hpair : ({u, v} : Finset (Fin x.n)) =
      {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2}) :
    (case3PairPosition u v = case3PairPosition ((case3InputEdges x)[k.1]).1 ((case3InputEdges x)[k.1]).2 ∨
      case3PairPosition u v = case3PairPosition ((case3InputEdges x)[k.1]).2 ((case3InputEdges x)[k.1]).1) ↔
      j = k := by
  constructor
  · intro h
    apply canonical_edge_eq_of_pair x j k
    rw [← hpair]
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := case3PairPosition_injective _ _ _ _ h
      rfl
    · obtain ⟨rfl, rfl⟩ := case3PairPosition_injective _ _ _ _ h
      exact Finset.pair_comm _ _
  · rintro rfl
    rcases pair_orientations _ _ _ _ hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem getD_set_at (l : List ℕ) (i j value : ℕ) (hj : j < l.length) :
    (l.set i value).getD j 0 = if j = i then value else l.getD j 0 := by
  rw [List.getD_eq_getElem _ 0 (by simpa only [List.length_set] using hj),
    List.getElem_set]
  by_cases h : j = i
  · simp only [h, ↓reduceIte]
  · simp only [h, Ne.symm h, ↓reduceIte, List.getD_eq_getElem _ 0 hj]

private theorem putEdgeLabel_getD {n : ℕ} (table : List ℕ) (u v : Fin n)
    (label target : ℕ) (htarget : target < table.length) :
    (case3PutEdgeLabel table u v label).getD target 0 =
      if target = case3PairPosition u v ∨ target = case3PairPosition v u then label
      else table.getD target 0 := by
  unfold case3PutEdgeLabel
  rw [getD_set_at _ _ _ _ (by simpa only [List.length_set] using htarget),
    getD_set_at _ _ _ _ htarget]
  by_cases h₁ : target = case3PairPosition u v <;>
    by_cases h₂ : target = case3PairPosition v u <;> simp only [h₁, h₂, ↓reduceIte, or_self,
      true_or, or_true, false_or, ite_self]

/-- Once an edge has been visited, either direction stores its exact owner label. -/
theorem case3EdgeMatrixPrefix_getD (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) (u v : Fin x.n)
    (hpair : ({u, v} : Finset (Fin x.n)) =
      {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2})
    (k : ℕ) (hk : k ≤ (case3InputEdges x).length) :
    (case3EdgeMatrixPrefix x Z k).getD (case3PairPosition u v) 0 =
      if j.1 < k then case3EdgeLabel x Z j else 0 := by
  induction k with
  | zero =>
    rw [case3EdgeMatrixPrefix_zero]
    change (List.replicate (x.n * x.n) (0 : ℕ)).getD (case3PairPosition u v) 0 = 0
    rw [List.getD_eq_getElem (List.replicate (x.n * x.n) (0 : ℕ)) 0
      (by simpa only [List.length_replicate] using case3PairPosition_lt u v)]
    simp only [List.getElem_replicate]
  | succ k ih =>
    have hkm : k < (case3InputEdges x).length := by omega
    rw [case3EdgeMatrixPrefix_succ x Z k hkm,
      putEdgeLabel_getD _ _ _ _ _ (by rw [case3EdgeMatrixPrefix_length]; exact case3PairPosition_lt u v)]
    simp only [target_collision x j ⟨k, hkm⟩ u v hpair]
    by_cases h : j = (⟨k, hkm⟩ : Fin (case3InputEdges x).length)
    · subst j
      simp only [↓reduceIte, Nat.lt_succ_self]
    · simp only [h, ↓reduceIte]
      rw [ih (by omega)]
      have hne : j.1 ≠ k := fun heq => h (Fin.ext heq)
      have hlt : j.1 < k + 1 ↔ j.1 < k := by omega
      simp only [hlt]

/-- In the complete matrix, the lookup is the edge's computed routing label. -/
theorem case3EdgeMatrix_getD (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) (u v : Fin x.n)
    (hpair : ({u, v} : Finset (Fin x.n)) =
      {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2}) :
    (case3EdgeMatrixPrefix x Z (case3InputEdges x).length).getD (case3PairPosition u v) 0 =
      case3EdgeLabel x Z j := by
  simpa only [j.2, ↓reduceIte] using case3EdgeMatrixPrefix_getD x Z j u v hpair _ le_rfl

/-- Either direction's endpoint-table label tests exact member adjacency. -/
theorem case3EdgeMatrix_adj_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) (u v : Fin x.n)
    (hpair : ({u, v} : Finset (Fin x.n)) =
      {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2})
    (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).graph.Adj u v ↔
      (case3EdgeMatrixPrefix x Z (case3InputEdges x).length).getD (case3PairPosition u v) 0 =
        case3RawIndexLabel x i.1 := by
  rw [case3EdgeMatrix_getD x Z j u v hpair, ← case3EdgeLabel_adj_iff x Z j i]
  rcases pair_orientations _ _ _ _ hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (case3SelectedMember x Z i).graph.adj_comm _ _

end GraphMinor.Compute
