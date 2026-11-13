module
public import GraphMinor.Thomason.GeometricDomination
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Lean.Elab.Tactic.Omega

/-!
# Selecting a geometrically dominating set outside exceptional families

In Thomason's main theorem, page 264 (1984), the sets which fail to
meet an earlier branch lie in a small exceptional set. The union bound
on their `k`-subsets leaves an almost-dominating set outside every such
exceptional family.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The selection argument in the main theorem, Thomason (1984), p. 264.
The selected almost-dominating set is contained in none of the exceptional
sets. -/
theorem exists_geometricDominatingSet_avoiding {I : Type v} [DecidableEq I]
    (S : Finset I) (B : I → Finset V) (t M D k : ℕ)
    (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hB : ∀ i ∈ S, (B i).card ≤ t)
    (hcount : S.card * t.choose k < M.choose k) :
    ∃ Y ∈ residualBoundedSets G k
      (Fintype.card V * D ^ k / (Fintype.card V + 1 - M) ^ k), ∀ i ∈ S, ¬ Y ⊆ B i := by
  let F := S.biUnion (fun i => (B i).powersetCard k)
  have hF : F.card ≤ S.card * t.choose k := by
    calc
      F.card ≤ ∑ i ∈ S, ((B i).powersetCard k).card := card_biUnion_le
      _ ≤ ∑ _i ∈ S, t.choose k := by
        apply sum_le_sum
        intro i hi
        rw [card_powersetCard]
        exact Nat.choose_le_choose k (hB i hi)
      _ = S.card * t.choose k := by simp
  have hlt : F.card < (residualBoundedSets G k
      (Fintype.card V * D ^ k / (Fintype.card V + 1 - M) ^ k)).card :=
    lt_of_le_of_lt hF (lt_of_lt_of_le hcount (card_residualBoundedSets_geometric G M D k hM hdegree))
  obtain ⟨Y, hY, hYF⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨Y, hY, ?_⟩
  intro i hi hsub
  apply hYF
  exact mem_biUnion.mpr ⟨i, hi, mem_powersetCard.mpr
    ⟨hsub, ((mem_residualBoundedSets_iff G k _ Y).mp hY).1⟩⟩

end GraphMinor.Thomason
