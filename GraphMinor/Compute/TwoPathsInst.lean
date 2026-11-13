module

public import GraphMinor.Compute.TwoPathsSplit
import GraphMinor.HP25.Prop52
import GraphMinor.HP25.Lemma43Tools

/-!
# The subinstances are instances

The recursion of Algorithm 5.1 calls itself on the two subinstances of a split. The next call
needs its cycle to be a cycle of its graph: `findProg` asks for a cycle without repeats, and the
completion step asks for a cycle of the graph (`IsSplitInput`). `isCycleList_sub` gives this, from
Proposition 5.1 (`SplitSetting.cycle₁`, `SplitSetting.cycle₂`, `GraphMinor/HP25/Prop52.lean`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {V : Type*} [DecidableEq V]

/-- **The cycles of the subinstances.** In the setting of `isCrossed_iff_sub`, the cycle of
subinstance `i` is a cycle of its graph, for `i = 1` and `i = 2`. -/
theorem isCycleList_sub {H F : SimpleGraph V} {a b : V} {A B m : List V}
    (hC : IsCycleList H (a :: A ++ b :: B)) (hA : A ≠ []) (hB : B ≠ [])
    {P' : (H ⊔ F).Walk a b} (hP' : IsTPath (H ⊔ F) (a :: A ++ b :: B) P')
    (hm : P'.support = a :: m ++ [b])
    (hsep : Separates (H ⊔ F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B}) :
    IsCycleList (subGraph (H ⊔ F) P'.support A 1) (subCycle a b A B m 1) ∧
      IsCycleList (subGraph (H ⊔ F) P'.support A 2) (subCycle a b A B m 2) := by
  obtain ⟨hcomp, h1, h2, h3, h4⟩ := isPathComposition_sides (hC.mono le_sup_left) hP' hsep
  have hs : SplitSetting (H ⊔ F) (a :: A ++ b :: B) a b A B m 0 P'
      (restrict (H ⊔ F) (sideOne (H ⊔ F) P'.support A))
      (restrict (H ⊔ F) (sideTwo (H ⊔ F) P'.support A))
      (sideOne (H ⊔ F) P'.support A) (sideTwo (H ⊔ F) P'.support A) :=
    ⟨hC.mono le_sup_left, by simp, hA, hB, hP', hm, hsep, hcomp, h1, h2, h3, h4⟩
  exact ⟨hs.cycle₁, hs.cycle₂⟩

omit [DecidableEq V] in
/-- The graph of a subinstance is a subgraph of `H ⊔ F`. -/
theorem subGraph_le (G : SimpleGraph V) (Pv A : List V) (i : ℕ) : subGraph G Pv A i ≤ G := by
  intro u v h
  rcases i with _ | _ | i
  · exact h.1
  · exact h.1
  · exact h.1

end GraphMinor.Compute.TwoPaths
