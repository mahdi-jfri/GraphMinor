module

public import GraphMinor.GM05.Defs
import GraphMinor.GM10.TreeWidthBasic

/-!
# Packing or hitting subtrees of a finite tree

Delete a leaf of the tree. If a member of the family consists of that leaf,
pack it and continue with members avoiding the leaf, or add the leaf to a
hitting set. Otherwise removing the leaf preserves nonemptiness and preserves
whether two members intersect. This is the packing fact used for circuits in
Graph Minors V, (8.1).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {ι J : Type*}

private lemma path_induced {T : SimpleGraph ι} (hT : T.IsTree)
    {S : Set ι} (hS : (T.induce S).Connected) {a b c : S}
    (h : OnTreePath (T.induce S) a b c) : OnTreePath T a.1 b.1 c.1 := by
  obtain ⟨p, hp⟩ := hS.exists_isPath a b
  let f : T.induce S →g T := ⟨Subtype.val, fun h ↦ h⟩
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  apply (GM10.onTreePath_iff_of_isPath hT hp').2
  rw [Walk.support_map]
  exact List.mem_map.mpr ⟨c, h p hp, rfl⟩

private lemma leaf_path {T : SimpleGraph ι} {t s q : ι}
    (huniq : ∀ z, T.Adj t z → z = s) (hne : q ≠ t) : OnTreePath T t q s := by
  intro p hp
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ z _ h p =>
    have hz : z = s := huniq z h
    exact List.mem_cons_of_mem _ (hz ▸ p.start_mem_support)

/-- Nonempty path-closed sets in a finite tree can be packed `k` at a time,
or all met by fewer than `k` vertices. -/
theorem subtrees_pack_or_hit [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    (A : J → Set ι) (hN : ∀ i, (A i).Nonempty)
    (hconv : ∀ i a, a ∈ A i → ∀ b, b ∈ A i → ∀ c,
      OnTreePath T a b c → c ∈ A i) (k : ℕ) :
    (∃ f : Fin k → J, Pairwise fun i j ↦ Disjoint (A (f i)) (A (f j))) ∨
      ∃ X : Set ι, X.ncard < k ∧ ∀ i, (X ∩ A i).Nonempty := by
  classical
  have main : ∀ n, ∀ (κ : Type _) [Fintype κ], Fintype.card κ = n →
      ∀ (T : SimpleGraph κ), T.IsTree → ∀ (I : Type _) (A : I → Set κ),
      (∀ i, (A i).Nonempty) →
      (∀ i a, a ∈ A i → ∀ b, b ∈ A i → ∀ c, OnTreePath T a b c → c ∈ A i) →
      ∀ k, (∃ f : Fin k → I, Pairwise fun i j ↦ Disjoint (A (f i)) (A (f j))) ∨
        ∃ X : Set κ, X.ncard < k ∧ ∀ i, (X ∩ A i).Nonempty := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro κ _ hcard T hT I A hN hconv k
      cases k with
      | zero => exact Or.inl ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
      | succ k =>
        by_cases hI : Nonempty I
        swap
        · exact Or.inr ⟨∅, by simp, fun i ↦ (hI ⟨i⟩).elim⟩
        obtain ⟨i₀⟩ := hI
        by_cases hk : k = 0
        · subst k
          left
          refine ⟨fun _ ↦ i₀, ?_⟩
          intro i j hij
          exact (hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))).elim
        by_cases hs : Subsingleton κ
        · obtain ⟨t⟩ := hT.connected.nonempty
          right
          refine ⟨{t}, by simp; omega, fun i ↦ ?_⟩
          obtain ⟨q, hq⟩ := hN i
          exact ⟨t, rfl, (@Subsingleton.elim _ hs q t) ▸ hq⟩
        · let : Nontrivial κ := not_subsingleton_iff_nontrivial.mp hs
          obtain ⟨t, ht⟩ := hT.exists_vert_degree_one_of_nontrivial
          obtain ⟨s, hts, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp ht
          let S : Set κ := {t}ᶜ
          have hsS : s ∈ S := hts.ne.symm
          have hconn : (T.induce S).Connected :=
            hT.connected.induce_compl_singleton_of_degree_eq_one ht
          have hT' : (T.induce S).IsTree := ⟨hconn, hT.isAcyclic.induce S⟩
          have hlt : Fintype.card S < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (x := t) (by simp [S])
          by_cases hsingle : ∃ i, A i = {t}
          · obtain ⟨i₁, hi₁⟩ := hsingle
            let I' := {i : I // t ∉ A i}
            let A' : I' → Set S := fun i ↦ {q | q.1 ∈ A i.1}
            have hN' : ∀ i, (A' i).Nonempty := by
              intro i
              obtain ⟨q, hq⟩ := hN i.1
              exact ⟨⟨q, fun he ↦ i.2 (he ▸ hq)⟩, hq⟩
            have hconv' : ∀ i a, a ∈ A' i → ∀ b, b ∈ A' i → ∀ c,
                OnTreePath (T.induce S) a b c → c ∈ A' i := by
              intro i a ha b hb c hp
              exact hconv i.1 a.1 ha b.1 hb c.1 (path_induced hT hconn hp)
            rcases ih _ hlt S rfl (T.induce S) hT' I' A' hN' hconv' k with
              ⟨f, hf⟩ | ⟨X, hX, hh⟩
            · left
              let g : Fin (k + 1) → I := Fin.cases i₁ (fun j ↦ (f j).1)
              refine ⟨g, ?_⟩
              intro a
              refine Fin.cases ?_ (fun a ↦ ?_) a
              · intro b
                refine Fin.cases ?_ (fun b ↦ ?_) b
                · intro hab
                  exact (hab rfl).elim
                · intro hab
                  change Disjoint (A i₁) (A (f b).1)
                  rw [hi₁]
                  exact disjoint_singleton_left.mpr (f b).2
              · intro b
                refine Fin.cases ?_ (fun b ↦ ?_) b
                · intro hab
                  change Disjoint (A (f a).1) (A i₁)
                  rw [hi₁]
                  exact disjoint_singleton_right.mpr (f a).2
                · intro hab
                  change Disjoint (A (f a).1) (A (f b).1)
                  rw [Set.disjoint_left]
                  intro q hqa hqb
                  have hqS : q ∈ S := fun he ↦ (f a).2 (he ▸ hqa)
                  exact Set.disjoint_left.mp (hf (fun he ↦ hab (congrArg Fin.succ he)))
                    (show (⟨q, hqS⟩ : S) ∈ A' (f a) from hqa) hqb
            · right
              refine ⟨insert t (Subtype.val '' X), ?_, fun i ↦ ?_⟩
              · have hc := ncard_insert_le t (Subtype.val '' X)
                rw [ncard_image_of_injective X Subtype.val_injective] at hc
                omega
              · by_cases hti : t ∈ A i
                · exact ⟨t, mem_insert t _, hti⟩
                · obtain ⟨q, hqX, hqA⟩ := hh ⟨i, hti⟩
                  exact ⟨q.1, Or.inr ⟨q, hqX, rfl⟩, hqA⟩
          · have hother : ∀ i, ∃ q ∈ A i, q ≠ t := by
              intro i
              by_contra hnone
              apply hsingle
              refine ⟨i, subset_antisymm (fun q hq ↦ ?_) ?_⟩
              · by_contra hqt
                exact hnone ⟨q, hq, hqt⟩
              · obtain ⟨q, hq⟩ := hN i
                have hqt : q = t := by by_contra h; exact hnone ⟨q, hq, h⟩
                exact singleton_subset_iff.mpr (hqt ▸ hq)
            let A' : I → Set S := fun i ↦ {q | q.1 ∈ A i}
            have hN' : ∀ i, (A' i).Nonempty := by
              intro i
              obtain ⟨q, hq, hqt⟩ := hother i
              exact ⟨⟨q, hqt⟩, hq⟩
            have hconv' : ∀ i a, a ∈ A' i → ∀ b, b ∈ A' i → ∀ c,
                OnTreePath (T.induce S) a b c → c ∈ A' i := by
              intro i a ha b hb c hp
              exact hconv i a.1 ha b.1 hb c.1 (path_induced hT hconn hp)
            have hstep : ∀ i, t ∈ A i → s ∈ A i := by
              intro i hti
              obtain ⟨q, hq, hqt⟩ := hother i
              exact hconv i t hti q hq s (leaf_path huniq hqt)
            rcases ih _ hlt S rfl (T.induce S) hT' I A' hN' hconv' (k + 1) with
              ⟨f, hf⟩ | ⟨X, hX, hh⟩
            · left
              refine ⟨f, fun a b hab ↦ ?_⟩
              change Disjoint (A (f a)) (A (f b))
              rw [Set.disjoint_left]
              intro q hqa hqb
              by_cases hqt : q = t
              · subst q
                exact Set.disjoint_left.mp (hf hab)
                  (show (⟨s, hsS⟩ : S) ∈ A' (f a) from hstep (f a) hqa)
                  (hstep (f b) hqb)
              · exact Set.disjoint_left.mp (hf hab)
                  (show (⟨q, hqt⟩ : S) ∈ A' (f a) from hqa) hqb
            · right
              refine ⟨Subtype.val '' X, ?_, fun i ↦ ?_⟩
              · rw [ncard_image_of_injective X Subtype.val_injective]
                exact hX
              · obtain ⟨q, hqX, hqA⟩ := hh i
                exact ⟨q.1, ⟨q, hqX, rfl⟩, hqA⟩
  exact main _ ι rfl T hT J A hN hconv k

end GraphMinor.GM05
