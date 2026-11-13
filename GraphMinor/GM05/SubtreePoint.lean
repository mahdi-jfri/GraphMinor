module

public import GraphMinor.GM05.Defs
import GraphMinor.GM10.TreeWidthBasic

/-!
# A subtree with a common meeting point

Remove leaves of the host tree until a member of the family consists of
a leaf. Every subtree meeting that member contains the leaf. If no member
is a singleton leaf, deleting the leaf preserves all intersections. This
provides the simplicial-vertex step for subtree intersection graphs.
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

/-- Some member of a nonempty family of subtrees has a point contained in
every member that meets it. The family itself need not be finite. -/
theorem exists_subtree_meeting_point [Fintype ι] [Nonempty J]
    {T : SimpleGraph ι} (hT : T.IsTree) (A : J → Set ι)
    (hN : ∀ i, (A i).Nonempty)
    (hconv : ∀ i a, a ∈ A i → ∀ b, b ∈ A i → ∀ c,
      OnTreePath T a b c → c ∈ A i) :
    ∃ i t, t ∈ A i ∧ ∀ j, (A i ∩ A j).Nonempty → t ∈ A j := by
  classical
  have main : ∀ n, ∀ (κ : Type _) [Fintype κ], Fintype.card κ = n →
      ∀ (T : SimpleGraph κ), T.IsTree → ∀ A : J → Set κ,
      (∀ i, (A i).Nonempty) →
      (∀ i a, a ∈ A i → ∀ b, b ∈ A i → ∀ c, OnTreePath T a b c → c ∈ A i) →
      ∃ i t, t ∈ A i ∧ ∀ j, (A i ∩ A j).Nonempty → t ∈ A j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro κ _ hcard T hT A hN hconv
      by_cases hs : Subsingleton κ
      · obtain ⟨i⟩ := ‹Nonempty J›
        obtain ⟨t,ht⟩ := hN i
        refine ⟨i,t,ht,fun j _ ↦ ?_⟩
        obtain ⟨q,hq⟩ := hN j
        exact (@Subsingleton.elim _ hs q t) ▸ hq
      · let : Nontrivial κ := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨t, ht⟩ := hT.exists_vert_degree_one_of_nontrivial
        obtain ⟨s, hts, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp ht
        by_cases hsing : ∃ i, A i ⊆ {t}
        · obtain ⟨i, hi⟩ := hsing
          obtain ⟨q,hq⟩ := hN i
          have hqt : q=t := hi hq
          refine ⟨i,t,hqt ▸ hq,fun j hj ↦ ?_⟩
          obtain ⟨p,hpi,hpj⟩ := hj
          exact (show p=t from hi hpi) ▸ hpj
        · have hother : ∀ i, ∃ q ∈ A i, q ≠ t := by
            intro i
            by_contra hnone
            apply hsing
            refine ⟨i, fun q hq ↦ ?_⟩
            by_contra hqt
            exact hnone ⟨q,hq,hqt⟩
          let S : Set κ := {t}ᶜ
          let A' : J → Set S := fun i ↦ {q | q.1 ∈ A i}
          have hsS : s ∈ S := hts.ne.symm
          have hconn : (T.induce S).Connected :=
            hT.connected.induce_compl_singleton_of_degree_eq_one ht
          have hT' : (T.induce S).IsTree := ⟨hconn,hT.isAcyclic.induce S⟩
          have hstep : ∀ i, t ∈ A i → s ∈ A i := by
            intro i hti
            obtain ⟨q,hq,hqt⟩ := hother i
            exact hconv i t hti q hq s (neighbour_on_path huniq hqt)
          have hN' : ∀ i, (A' i).Nonempty := by
            intro i
            obtain ⟨q,hq,hqt⟩ := hother i
            exact ⟨⟨q,hqt⟩,hq⟩
          have hconv' : ∀ i a, a ∈ A' i → ∀ b, b ∈ A' i → ∀ c,
              OnTreePath (T.induce S) a b c → c ∈ A' i := by
            intro i a ha b hb c hp
            exact hconv i a.1 ha b.1 hb c.1 (path_in_induced hT hconn hp)
          have hlt : Fintype.card S < n := by
            rw [←hcard]
            exact Fintype.card_subtype_lt (x:=t) (by simp [S])
          obtain ⟨i,q,hq,hm⟩ := ih _ hlt S rfl (T.induce S) hT' A' hN' hconv'
          refine ⟨i,q.1,hq,fun j hj ↦ hm j ?_⟩
          obtain ⟨p,hpi,hpj⟩ := hj
          by_cases hpt : p=t
          · subst p
            exact ⟨⟨s,hsS⟩,hstep i hpi,hstep j hpj⟩
          · exact ⟨⟨p,hpt⟩,hpi,hpj⟩
  exact main _ ι rfl T hT A hN hconv

end GraphMinor.GM05
