module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.Simplicial
import GraphMinor.GM05.IndependentRepresentatives
import GraphMinor.GM05.IndependentRestriction
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Prescribed counts in disjoint independent sets

This is the induction of Graph Minors V, (8.5). First remove vertices
outside the independent sets. Choose a simplicial vertex. If its color
has target zero, omit that color and apply induction. Otherwise remove
one representative from every color, decrease the chosen target, apply
induction, and put the simplicial vertex back. Every neighbor was removed,
so the resulting set remains independent.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set
open scoped BigOperators

universe u

/-- The strengthened form of Graph Minors V, (8.5), with the selected set
contained in the union of the given independent sets. The proof follows
the induction on pages 110–111. -/
theorem independent_selection_subset {V : Type u} [Finite V] {I : Type} [Fintype I]
    {G : SimpleGraph V} (hG : IsChordal G) (Z : I → Set V)
    (hZ : ∀ i, G.IsIndepSet (Z i)) (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    {k : ℕ} (hcard : ∀ i, (Z i).ncard=k) (x : I → ℕ) (hsum : ∑ i,x i=k) :
    ∃ X : Set V, X⊆⋃ i,Z i ∧ G.IsIndepSet X ∧ ∀ i,(X∩Z i).ncard=x i := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have main : ∀ n, ∀ (W : Type u) [Fintype W], Fintype.card W=n →
      ∀ (I : Type) [Fintype I] (G : SimpleGraph W), IsChordal G →
      ∀ (Z : I → Set W), (∀ i, G.IsIndepSet (Z i)) →
      Pairwise (fun i j ↦ Disjoint (Z i) (Z j)) →
      ∀ k, (∀ i, (Z i).ncard=k) → ∀ x : I → ℕ, (∑ i,x i)=k →
      ∃ X : Set W, X⊆⋃ i,Z i ∧ G.IsIndepSet X ∧ ∀ i,(X∩Z i).ncard=x i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ hW I _ G hG Z hZ hdisj k hcard x hsum
      by_cases hzero : ∀ i,x i=0
      · refine ⟨∅,empty_subset _,?_,?_⟩
        · intro a ha; exact (notMem_empty a ha).elim
        · intro i; simp [hzero i]
      have hpos : 0<k := by
        by_contra hn
        have hk : k=0 := by omega
        apply hzero
        intro i
        have hi : x i≤∑ j,x j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hN : ∀ i,(Z i).Nonempty := by
        intro i
        exact (ncard_pos (toFinite _)).mp (by rw [hcard i]; exact hpos)
      by_cases hout : ∃ v, v∉⋃ i,Z i
      · obtain ⟨v,hv⟩ := hout
        let U := ⋃ i,Z i
        let Z' (i : I) : Set U := {a | a.1∈Z i}
        have hZU : ∀ i,Z i⊆U := fun i ↦ subset_iUnion Z i
        have hlt : Fintype.card U<n := by
          rw [←hW]
          exact Fintype.card_subtype_lt (x:=v) hv
        have hGU := hG.of_embedding (Embedding.induce U)
        have hZ' : ∀ i,(G.induce U).IsIndepSet (Z' i) :=
          fun i ↦ (restrict_independent_set (hZ i) (hZU i)).1
        have hcard' : ∀ i,(Z' i).ncard=k := fun i ↦
          (restrict_independent_set (hZ i) (hZU i)).2.trans (hcard i)
        obtain ⟨X,hX,hind,hcounts⟩ := ih _ hlt U rfl I (G.induce U) hGU Z' hZ'
          (disjoint_restrict Z hdisj) k hcard' x hsum
        refine ⟨Subtype.val '' X,image_subset_iUnion hX,indepSet_image_induce hind,?_⟩
        intro i
        rw [ncard_image_val_inter]
        exact hcounts i
      · have hcover : ⋃ i,Z i=univ := by
          apply eq_univ_of_forall
          intro v
          by_contra hv
          exact hout ⟨v,hv⟩
        have hI : Nonempty I := by
          by_contra hn
          apply hzero
          intro i
          exact (hn ⟨i⟩).elim
        obtain ⟨i₀⟩ := hI
        obtain ⟨v₀,hv₀⟩ := hN i₀
        let : Nonempty W := ⟨v₀⟩
        obtain ⟨v,hvS⟩ := theorem_8_4_proof G hG
        have hvU : v∈⋃ i,Z i := hcover.symm ▸ mem_univ v
        obtain ⟨j,hvj⟩ := mem_iUnion.mp hvU
        by_cases hj : x j=0
        · let J := {i : I // i≠j}
          let U := ⋃ i : J,Z i.1
          let Z' (i : J) : Set U := {a | a.1∈Z i.1}
          have hvnot : v∉U := by
            intro h
            obtain ⟨i,hi⟩ := mem_iUnion.mp h
            exact Set.disjoint_left.mp (hdisj i.2) hi hvj
          have hlt : Fintype.card U<n := by
            rw [←hW]
            exact Fintype.card_subtype_lt (x:=v) hvnot
          have hZU : ∀ i : J,Z i.1⊆U := fun i ↦ subset_iUnion (fun i : J ↦ Z i.1) i
          have hZ' : ∀ i,(G.induce U).IsIndepSet (Z' i) :=
            fun i ↦ (restrict_independent_set (hZ i.1) (hZU i)).1
          have hdisj' : Pairwise (fun i l : J ↦ Disjoint (Z i.1) (Z l.1)) := by
            intro i l hil
            exact hdisj (fun he ↦ hil (Subtype.ext he))
          have hcard' : ∀ i,(Z' i).ncard=k := fun i ↦
            (restrict_independent_set (hZ i.1) (hZU i)).2.trans (hcard i.1)
          have hsum' : (∑ i : J,x i.1)=k := (sum_subtype_ne_of_zero x j hj).trans hsum
          obtain ⟨X,hX,hind,hcounts⟩ := ih _ hlt U rfl J (G.induce U)
            (hG.of_embedding (Embedding.induce U)) Z' hZ'
            (disjoint_restrict (fun i : J ↦ Z i.1) hdisj') k hcard' (fun i ↦ x i.1) hsum'
          let Y := Subtype.val '' X
          have hYsub : Y⊆⋃ i : J,Z i.1 := image_subset_iUnion hX
          refine ⟨Y,?_,indepSet_image_induce hind,?_⟩
          · intro a ha
            obtain ⟨i,hi⟩ := mem_iUnion.mp (hYsub ha)
            exact mem_iUnion.mpr ⟨i.1,hi⟩
          · intro i
            by_cases hij : i=j
            · subst i
              have he : Y∩Z j=∅ := by
                apply eq_empty_iff_forall_notMem.mpr
                rintro a ⟨ha,haj⟩
                obtain ⟨i,hi⟩ := mem_iUnion.mp (hYsub ha)
                exact Set.disjoint_left.mp (hdisj i.2) hi haj
              rw [he,ncard_empty,hj]
            · rw [ncard_image_val_inter]
              exact hcounts ⟨i,hij⟩
        · have hjpos : 0<x j := Nat.pos_of_ne_zero hj
          obtain ⟨z,hz,hzj,hneigh⟩ := lemma_8_5_neighbours_are_representatives hvS hZ hN hvj
            (fun u _ ↦ mem_iUnion.mp (hcover.symm ▸ mem_univ u))
          let U := (range z)ᶜ
          let Z' (i : I) : Set U := {a | a.1∈Z i}
          let x' := Function.update x j (x j-1)
          have hvnot : v∉U := fun h ↦ h ⟨j,hzj⟩
          have hlt : Fintype.card U<n := by
            rw [←hW]
            exact Fintype.card_subtype_lt (x:=v) hvnot
          have hZ' : ∀ i,(G.induce U).IsIndepSet (Z' i) := by
            intro i a ha b hb hab hadj
            exact hZ i ha hb (fun he ↦ hab (Subtype.ext he)) hadj
          have hcard' : ∀ i,(Z' i).ncard=k-1 := by
            intro i
            rw [ncard_subtype]
            change (Z i∩(range z)ᶜ).ncard=k-1
            exact ncard_residual_representatives hdisj hz hcard i
          have hsum' : (∑ i,x' i)=k-1 := (sum_update_pred x j hjpos).trans (congrArg (fun n ↦ n-1) hsum)
          obtain ⟨X,hX,hind,hcounts⟩ := ih _ hlt U rfl I (G.induce U)
            (hG.of_embedding (Embedding.induce U)) Z' hZ' (disjoint_restrict Z hdisj)
            (k-1) hcard' x' hsum'
          let Y := Subtype.val '' X
          have hYsub : Y⊆⋃ i,Z i := image_subset_iUnion hX
          have hYU : Y⊆U := by rintro a ⟨q,hq,rfl⟩; exact q.2
          have hvY : v∉Y := fun h ↦ hvnot (hYU h)
          have hYind : G.IsIndepSet Y := indepSet_image_induce hind
          refine ⟨insert v Y,?_,?_,?_⟩
          · intro a ha
            rcases ha with rfl|ha
            · exact mem_iUnion.mpr ⟨j,hvj⟩
            · exact hYsub ha
          · intro a ha b hb hab hadj
            rcases ha with rfl|ha
            · rcases hb with rfl|hb
              · exact hadj.ne rfl
              · exact hYU hb (hneigh b hadj)
            · rcases hb with rfl|hb
              · exact hYU ha (hneigh a hadj.symm)
              · exact hYind ha hb hab hadj
          · intro i
            have hcountY : (Y∩Z i).ncard=x' i := by
              rw [ncard_image_val_inter]
              exact hcounts i
            by_cases hij : i=j
            · subst i
              have he : insert v Y∩Z j=insert v (Y∩Z j) := by
                ext a
                simp only [mem_inter_iff,mem_insert_iff]
                constructor
                · rintro ⟨rfl|ha,haj⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨ha,haj⟩
                · rintro (rfl|⟨ha,haj⟩)
                  · exact ⟨Or.inl rfl,hvj⟩
                  · exact ⟨Or.inr ha,haj⟩
              rw [he,ncard_insert_of_notMem (fun h ↦ hvY h.1),hcountY]
              simp only [x',Function.update_self]
              omega
            · have hvZi : v∉Z i := fun h ↦ Set.disjoint_left.mp (hdisj hij) h hvj
              have he : insert v Y∩Z i=Y∩Z i := by
                ext a
                constructor
                · rintro ⟨rfl|ha,hai⟩
                  · exact (hvZi hai).elim
                  · exact ⟨ha,hai⟩
                · rintro ⟨ha,hai⟩
                  exact ⟨Or.inr ha,hai⟩
              rw [he,hcountY]
              exact Function.update_of_ne hij _ _
  exact main _ V rfl I G hG Z hZ hdisj k hcard x hsum

/-- Graph Minors V, (8.5), pages 110–111: disjoint independent sets of
cardinality `k` in a chordal graph have an independent selection with
prescribed intersection sizes whose sum is `k`. The proof is the paper's
simplicial-vertex induction. -/
theorem theorem_8_5_proof {V : Type u} [Finite V] {m k : ℕ} {G : SimpleGraph V}
    (hG : IsChordal G) (Z : Fin m → Set V) (hZ : ∀ i,G.IsIndepSet (Z i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j)))
    (hcard : ∀ i,(Z i).ncard=k) (x : Fin m → ℕ) (hsum : ∑ i,x i=k) :
    ∃ X : Set V, G.IsIndepSet X ∧ ∀ i,(X∩Z i).ncard=x i := by
  obtain ⟨X,_,hX,hcounts⟩ := independent_selection_subset hG Z hZ hdisj hcard x hsum
  exact ⟨X,hX,hcounts⟩

end GraphMinor.GM05
