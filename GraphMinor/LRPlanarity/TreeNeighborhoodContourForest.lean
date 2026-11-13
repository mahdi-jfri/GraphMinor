module

public import GraphMinor.LRPlanarity.Defs
import GraphMinor.LRPlanarity.TreeNeighborhoodForest

/-!
# Forest bounds for the contour recursion

Part IV, Section 7b of the planarity note recursively substitutes each
child contour for its tree incidence. The finite forest bounds this
recursion. There is an ancestor at every smaller search depth, so all
depths are below the number of vertices. Two ancestors of one vertex are
comparable, and ancestors at equal depth coincide. These facts keep the
child contour blocks disjoint and justify the specified finite fuel.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Every smaller depth occurs on the parent path to a vertex. -/
theorem exists_ancestor_at_depth {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (v : Fin N) (i : ℕ) (hi : i ≤ T.depth v) :
    ∃ u, T.Ancestor u v ∧ T.depth u = i := by
  suffices ∀ n, ∀ v : Fin N, T.depth v = n → ∀ i ≤ n,
      ∃ u, T.Ancestor u v ∧ T.depth u = i from this _ v rfl i hi
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv i hi
    by_cases hei : i = n
    · exact ⟨v,Relation.ReflTransGen.refl,hv.trans hei.symm⟩
    have hin : i < n := lt_of_le_of_ne hi hei
    cases hp : T.parent v with
    | none =>
      have hn : n = 0 := hv.symm.trans (hT.1 v hp)
      exact (Nat.not_lt_zero i (hn ▸ hin)).elim
    | some p =>
      have hdepth := (hT.2.1 p v hp).2
      have hpn : T.depth p < n := by
        rw [← hv,hdepth]
        exact Nat.lt_succ_self _
      have hip : i ≤ T.depth p := by
        rw [← hv,hdepth] at hin
        exact Nat.le_of_lt_succ hin
      obtain ⟨u,hu,hui⟩ := ih _ hpn p rfl i hip
      exact ⟨u,hu.tail hp,hui⟩

/-- Search depth is strictly below the number of vertices. -/
theorem dfs_depth_lt_card {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (v : Fin N) : T.depth v < N := by
  classical
  have hanc : ∀ i : Fin (T.depth v + 1), ∃ u : Fin N, T.Ancestor u v ∧ T.depth u = i.val :=
    fun i => exists_ancestor_at_depth hT v i.val (Nat.le_of_lt_succ i.isLt)
  choose f hf using hanc
  have hinj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact (hf i).2.symm.trans ((congrArg T.depth he).trans (hf j).2)
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  exact Nat.lt_of_succ_le hcard

/-- Two ancestors of a common descendant are comparable along the unique
parent path. -/
theorem ancestors_comparable {N : ℕ} {T : Forest N} {u v x : Fin N}
    (hu : T.Ancestor u x) (hv : T.Ancestor v x) : T.Ancestor u v ∨ T.Ancestor v u := by
  induction hu generalizing v with
  | refl => exact Or.inr hv
  | @tail p x hprefix hparent ih =>
    cases hv with
    | refl => exact Or.inl (hprefix.tail hparent)
    | @tail q x hvq hpq =>
      have he : q = p := Option.some.inj (hpq.symm.trans hparent)
      subst q
      exact ih hvq

/-- Equal-depth ancestors of one vertex are equal. -/
theorem equal_depth_ancestors_eq {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) {u v x : Fin N} (hu : T.Ancestor u x) (hv : T.Ancestor v x)
    (hdepth : T.depth u = T.depth v) : u = v := by
  by_contra hne
  rcases ancestors_comparable hu hv with huv | hvu
  · exact (ne_of_lt (strict_ancestor_depth_lt hT huv hne)) hdepth
  · exact (ne_of_lt (strict_ancestor_depth_lt hT hvu (Ne.symm hne))) hdepth.symm

end GraphMinor.LRPlanarity
