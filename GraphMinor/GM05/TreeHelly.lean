module

public import GraphMinor.GM05.Defs
import GraphMinor.GM10.TreeWidthBasic

/-!
# A common vertex of pairwise intersecting subtrees

The grid lower bound in Graph Minors V, (1.4), uses the fact that pairwise
intersecting subtrees of a finite tree have a common vertex. Delete a leaf.
If one subtree is just that leaf, pairwise intersection proves the result.
Otherwise all the subtrees still meet pairwise after the leaf is removed.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {ι J : Type*}

private lemma path_in_induced {T : SimpleGraph ι} (hT : T.IsTree)
    {S : Set ι} (hS : (T.induce S).Connected) {a b c : S}
    (h : OnTreePath (T.induce S) a b c) : OnTreePath T a.1 b.1 c.1 := by
  obtain ⟨p, hp⟩ := hS.exists_isPath a b
  let f : T.induce S →g T := ⟨Subtype.val, fun h ↦ h⟩
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  apply (GM10.onTreePath_iff_of_isPath hT hp').2
  rw [Walk.support_map]
  exact List.mem_map.mpr ⟨c, h p hp, rfl⟩

private lemma neighbour_on_path {T : SimpleGraph ι} {t s q : ι}
    (huniq : ∀ z, T.Adj t z → z = s) (hne : q ≠ t) : OnTreePath T t q s := by
  intro p hp
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ z _ h p =>
    have hz : z = s := huniq z h
    exact List.mem_cons_of_mem _ (hz ▸ p.start_mem_support)

/-- A family of nonempty path-closed vertex sets in a finite tree has a common
vertex whenever every two members intersect. The index set need not be finite. -/
theorem tree_helly [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    (A : J → Set ι)
    (hconv : ∀ i a, a ∈ A i → ∀ b, b ∈ A i → ∀ c,
      OnTreePath T a b c → c ∈ A i)
    (hpair : ∀ i j, (A i ∩ A j).Nonempty) :
    ∃ t, ∀ i, t ∈ A i := by
  classical
  have main : ∀ n, ∀ (κ : Type _) [Fintype κ], Fintype.card κ = n →
      ∀ (T : SimpleGraph κ), T.IsTree → ∀ A : J → Set κ,
      (∀ i a, a ∈ A i → ∀ b, b ∈ A i → ∀ c, OnTreePath T a b c → c ∈ A i) →
      (∀ i j, (A i ∩ A j).Nonempty) → ∃ t, ∀ i, t ∈ A i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro κ _ hcard T hT A hconv hpair
      by_cases hs : Subsingleton κ
      · obtain ⟨t⟩ := hT.connected.nonempty
        refine ⟨t, fun i ↦ ?_⟩
        obtain ⟨q, hq, _⟩ := hpair i i
        exact (@Subsingleton.elim _ hs q t) ▸ hq
      · let : Nontrivial κ := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨t, ht⟩ := hT.exists_vert_degree_one_of_nontrivial
        obtain ⟨s, hts, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp ht
        by_cases hsing : ∃ i, A i ⊆ {t}
        · obtain ⟨i, hi⟩ := hsing
          refine ⟨t, fun j ↦ ?_⟩
          obtain ⟨q, hqi, hqj⟩ := hpair i j
          have he : q = t := hi hqi
          exact he ▸ hqj
        · have hother : ∀ i, ∃ q ∈ A i, q ≠ t := by
            intro i
            by_contra hnone
            apply hsing
            refine ⟨i, fun q hq ↦ ?_⟩
            by_contra hqt
            exact hnone ⟨q, hq, hqt⟩
          let S : Set κ := {t}ᶜ
          let A' : J → Set S := fun i ↦ {q | q.1 ∈ A i}
          have hsS : s ∈ S := hts.ne.symm
          have hconn : (T.induce S).Connected :=
            hT.connected.induce_compl_singleton_of_degree_eq_one ht
          have hT' : (T.induce S).IsTree := ⟨hconn, hT.isAcyclic.induce S⟩
          have hstep : ∀ i, t ∈ A i → s ∈ A i := by
            intro i hti
            obtain ⟨q, hq, hqt⟩ := hother i
            exact hconv i t hti q hq s (neighbour_on_path huniq hqt)
          have hconv' : ∀ i a, a ∈ A' i → ∀ b, b ∈ A' i → ∀ c,
              OnTreePath (T.induce S) a b c → c ∈ A' i := by
            intro i a ha b hb c hp
            exact hconv i a.1 ha b.1 hb c.1 (path_in_induced hT hconn hp)
          have hpair' : ∀ i j, (A' i ∩ A' j).Nonempty := by
            intro i j
            obtain ⟨q, hqi, hqj⟩ := hpair i j
            by_cases hqt : q = t
            · subst q
              exact ⟨⟨s, hsS⟩, hstep i hqi, hstep j hqj⟩
            · exact ⟨⟨q, hqt⟩, hqi, hqj⟩
          have hlt : Fintype.card S < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := t) (by simp [S])
          obtain ⟨q, hq⟩ := ih _ hlt S rfl (T.induce S) hT' A' hconv' hpair'
          exact ⟨q.1, hq⟩
  exact main _ ι rfl T hT A hconv hpair

end GraphMinor.GM05
