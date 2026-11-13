module

public import GraphMinor.GM13.Section5b
public import GraphMinor.Menger.SimpleGraph

/-!
# Graph Minors XIII, Section 5 (Part C): Separation Step of (5.3)

This file formalizes Claim (1) (`theorem_5_3_step_sep`, separation and Menger's theorem)
in the proof of (5.3) of Graph Minors XIII (page 80).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v}

/-- Given a separation `(A, B)` of `G` and a subdigraph `S` of `G`, any walk in `S` from
`u ∈ B.vertexSet` to `w ∈ A.vertexSet` has a prefix in `G.interSub S B` ending in
`(A.vertexSet ∩ B.vertexSet) ∩ S.vertexSet`. -/
lemma GraphWalk.exists_prefix_in_right_to_sep {G A B S : Digraph α β}
    (hsep : G.IsSeparation A B) (hS : S.IsSubdigraph G)
    {u w : α} (W : GraphWalk S.toGraph u w)
    (huB : u ∈ B.vertexSet) (hwA : w ∈ A.vertexSet) :
    ∃ z' ∈ (A.vertexSet ∩ B.vertexSet) ∩ (G.interSub S B).vertexSet,
      Nonempty (GraphWalk (G.interSub S B).toGraph u z') := by
  induction W with
  | @nil x hxS =>
    have hxG : x ∈ G.vertexSet := hS.vertexSet_subset hxS
    have hxSB : x ∈ (G.interSub S B).vertexSet := ⟨hxG, hxS, huB⟩
    exact ⟨x, ⟨⟨hwA, huB⟩, hxSB⟩, ⟨.nil hxSB⟩⟩
  | @cons x y w e hlink W' ih =>
    have hxS : x ∈ S.vertexSet := S.toGraph.left_mem_of_isLink hlink
    have hxG : x ∈ G.vertexSet := hS.vertexSet_subset hxS
    have hxSB : x ∈ (G.interSub S B).vertexSet := ⟨hxG, hxS, huB⟩
    by_cases hxA : x ∈ A.vertexSet
    · exact ⟨x, ⟨⟨hxA, huB⟩, hxSB⟩, ⟨.nil hxSB⟩⟩
    · have heS : e ∈ S.edgeSet := hlink.1
      have heG : e ∈ G.edgeSet := hS.edgeSet_subset heS
      have hlinkG : G.toGraph.IsLink e x y := hS.toGraph_le.isLink_mono hlink
      have heNotA : e ∉ A.edgeSet := by
        intro heA
        rcases hlinkG.2 with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hxA (h1 ▸ hsep.sub_left.head_eq heA ▸ A.head_mem heA)
        · exact hxA (h2 ▸ hsep.sub_left.tail_eq heA ▸ A.tail_mem heA)
      have heB : e ∈ B.edgeSet := by
        have heAB : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union ▸ heG
        exact heAB.resolve_left heNotA
      have hyB : y ∈ B.vertexSet := by
        rcases hlinkG.2 with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2 ▸ hsep.sub_right.tail_eq heB ▸ B.tail_mem heB
        · exact h1 ▸ hsep.sub_right.head_eq heB ▸ B.head_mem heB
      have heSB : e ∈ (G.interSub S B).edgeSet := by
        refine ⟨⟨heG, heS, heB⟩, ?_, ?_⟩
        · exact ⟨hS.head_eq heS ▸ S.head_mem heS, hsep.sub_right.head_eq heB ▸ B.head_mem heB⟩
        · exact ⟨hS.tail_eq heS ▸ S.tail_mem heS, hsep.sub_right.tail_eq heB ▸ B.tail_mem heB⟩
      have hlinkSB : (G.interSub S B).toGraph.IsLink e x y := ⟨heSB, hlinkG.2⟩
      rcases ih hyB hwA with ⟨z', hz', ⟨W''⟩⟩
      exact ⟨z', hz', ⟨.cons hlinkSB W''⟩⟩

/-- Separation step (Claim (1) of Graph Minors XIII, (5.3), page 80):
if `(A, B)` is a separation of `G` of order `≤ ξ` with `Z ⊆ A.vertexSet` and `A ∩ sub i₁` null,
then applying the induction hypothesis to `(B, Z' = A.vertexSet ∩ B.vertexSet, sub i ∩ B)` and
attaching `ξ` vertex-disjoint paths in `A` from `Z` to `Z'` (by Menger's theorem) yields `H` in `G`. -/
theorem theorem_5_3_step_sep {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A₀ B₀ : Digraph α β),
      G.IsSeparation A₀ B₀ → Z ⊆ A₀.vertexSet → (G.interSub A₀ (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A₀ B₀)
    (i₁ : Fin k) (A B : Digraph α β)
    (hsep : G.IsSeparation A B) (hZA : Z ⊆ A.vertexSet)
    (hAnull₁ : (G.interSub A (sub i₁)).IsNull)
    (hord_le : Digraph.separationOrder A B ≤ ξ)
    (ih : ∀ (Z' : Set α) (sub' : Fin k → Digraph α β),
      B.IsFinite → Z' ⊆ B.vertexSet → Z'.ncard = ξ →
      (∀ i, (sub' i).IsSubdigraph B) →
      Pairwise (fun i j => Disjoint (sub' i).vertexSet (sub' j).vertexSet) →
      (∀ i, (sub' i).IsConnected ∨
        ((sub' i).vertexSet.Nonempty ∧
          ∀ u ∈ (sub' i).vertexSet, ∃ z' ∈ Z' ∩ (sub' i).vertexSet,
            Nonempty (GraphWalk (sub' i).toGraph u z'))) →
      (∀ i j, i < j →
        (((sub' i).vertexSet ∩ Z').Nonempty ∧ ((sub' j).vertexSet ∩ Z').Nonempty) ∨
          B.HasEdgeBetween (sub' i).vertexSet (sub' j).vertexSet) →
      (∀ i A' B', B.IsSeparation A' B' → Z' ⊆ A'.vertexSet →
        (B.interSub A' (sub' i)).IsNull → ξ ≤ Digraph.separationOrder A' B') →
      ∃ (μ : ℕ) (_ : μ ≤ ξ) (H' : Fin (k - (ξ - μ) / 2) → Digraph α β),
        (∀ i, (H' i).IsSubdigraph B) ∧
        (∀ i, (H' i).IsConnected) ∧
        Pairwise (fun i j => Disjoint (H' i).vertexSet (H' j).vertexSet) ∧
        (∀ i : Fin (k - (ξ - μ) / 2),
          (i.1 < ξ → ((H' i).vertexSet ∩ Z').ncard = 1) ∧
          (ξ ≤ i.1 → (H' i).vertexSet ∩ Z' = ∅)) ∧
        (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
          ¬ B.HasEdgeBetween (H' i).vertexSet (H' j).vertexSet → i.1 < μ ∧ j.1 < μ)) :
    ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) := by
  let Z' : Set α := A.vertexSet ∩ B.vertexSet
  have hord_ge : ξ ≤ Digraph.separationOrder A B := hiii i₁ A B hsep hZA hAnull₁
  have hZ'card : Z'.ncard = ξ := le_antisymm hord_le hord_ge
  have hBfin : B.IsFinite := ⟨hfin.finite_V.subset hsep.sub_right.vertexSet_subset,
    hfin.finite_E.subset hsep.sub_right.edgeSet_subset⟩
  have hAfin : A.IsFinite := ⟨hfin.finite_V.subset hsep.sub_left.vertexSet_subset,
    hfin.finite_E.subset hsep.sub_left.edgeSet_subset⟩
  have hZ'fin : Z'.Finite := hBfin.finite_V.subset inter_subset_right
  have hZfin : Z.Finite := hfin.finite_V.subset hZ
  let sub' (i : Fin k) : Digraph α β := G.interSub (sub i) B
  have hsub'V (i : Fin k) : (sub' i).vertexSet = (sub i).vertexSet ∩ B.vertexSet :=
    inter_eq_self_of_subset_right (inter_subset_left.trans (hsub i).vertexSet_subset)
  have hsub'_sub (i : Fin k) : (sub' i).IsSubdigraph B := {
    vertexSet_subset := by rw [hsub'V]; exact inter_subset_right
    edgeSet_subset := fun _ he => he.1.2.2
    head_eq := fun _ he => (hsep.sub_right.head_eq he.1.2.2).symm
    tail_eq := fun _ he => (hsep.sub_right.tail_eq he.1.2.2).symm
  }
  have hdisj' : Pairwise (fun i j => Disjoint (sub' i).vertexSet (sub' j).vertexSet) := by
    intro i j hij
    rw [hsub'V, hsub'V]
    exact (hdisj hij).mono inter_subset_left inter_subset_left
  -- Key helper: `A.vertexSet ∩ (sub i₁).vertexSet = ∅`
  have hi₁A_emp : A.vertexSet ∩ (sub i₁).vertexSet = ∅ := by
    have h1 := hAnull₁.1
    simp only [Digraph.interSub, Digraph.subdigraphOf] at h1
    rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep.sub_left.vertexSet_subset)] at h1
    exact h1
  have hi₁Z_emp : (sub i₁).vertexSet ∩ Z = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxi₁ hxZ
    have h : x ∈ A.vertexSet ∩ (sub i₁).vertexSet := ⟨hZA hxZ, hxi₁⟩
    rw [hi₁A_emp] at h
    exact h
  -- Every `sub i` meets `B.vertexSet`: if `i = i₁`, `(sub i₁).vertexSet ⊆ B.vertexSet`;
  -- if `i ≠ i₁`, by `hii` there is an edge between `sub i` and `sub i₁`, which must be in `B`.
  have hsub_meets_B (i : Fin k) : ((sub i).vertexSet ∩ B.vertexSet).Nonempty := by
    by_cases hii₁ : i = i₁
    · subst hii₁
      have hne : (sub i).vertexSet.Nonempty := by
        rcases hi i with ⟨hne, _⟩ | ⟨hne, _⟩ <;> exact hne
      rcases hne with ⟨u, hui⟩
      have huG : u ∈ G.vertexSet := (hsub i).vertexSet_subset hui
      rw [← hsep.vertexSet_union] at huG
      rcases huG with huA | huB
      · have h : u ∈ A.vertexSet ∩ (sub i).vertexSet := ⟨huA, hui⟩
        rw [hi₁A_emp] at h
        exact False.elim h
      · exact ⟨u, hui, huB⟩
    · have hEdge : G.HasEdgeBetween (sub i).vertexSet (sub i₁).vertexSet := by
        rcases lt_or_gt_of_ne hii₁ with hlt | hgt
        · rcases hii i i₁ hlt with ⟨_, h2⟩ | hE
          · rw [hi₁Z_emp] at h2; exact False.elim (not_nonempty_empty h2)
          · exact hE
        · rcases hii i₁ i hgt with ⟨h1, _⟩ | ⟨e, he, hE⟩
          · rw [hi₁Z_emp] at h1; exact False.elim (not_nonempty_empty h1)
          · exact ⟨e, he, hE.symm⟩
      rcases hEdge with ⟨e, heG, h⟩
      have heNotA : e ∉ A.edgeSet := by
        intro heA
        rcases h with ⟨_, ht⟩ | ⟨hh, _⟩
        · have hmem : G.tail e ∈ A.vertexSet ∩ (sub i₁).vertexSet :=
            ⟨hsep.sub_left.tail_eq heA ▸ A.tail_mem heA, ht⟩
          rw [hi₁A_emp] at hmem; exact hmem
        · have hmem : G.head e ∈ A.vertexSet ∩ (sub i₁).vertexSet :=
            ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hh⟩
          rw [hi₁A_emp] at hmem; exact hmem
      have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
      rcases h with ⟨hh, _⟩ | ⟨_, ht⟩
      · exact ⟨G.head e, hh, hsep.sub_right.head_eq heB ▸ B.head_mem heB⟩
      · exact ⟨G.tail e, ht, hsep.sub_right.tail_eq heB ▸ B.tail_mem heB⟩
  -- Key lemma: if `(sub' i).vertexSet ∩ Z' = ∅`, then `A.vertexSet ∩ (sub i).vertexSet = ∅`
  -- and `sub' i = sub i` is connected.
  have hsub_disj_A_of_disj_Z' (i : Fin k) (hdisjZ' : (sub' i).vertexSet ∩ Z' = ∅) :
      A.vertexSet ∩ (sub i).vertexSet = ∅ ∧
      (∀ u v, Nonempty (GraphWalk (sub i).toGraph u v) →
        Nonempty (GraphWalk (sub' i).toGraph u v)) := by
    have hA_emp : A.vertexSet ∩ (sub i).vertexSet = ∅ := by
      ext w
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hwA hwi
      rcases hsub_meets_B i with ⟨u₀, hu₀i, hu₀B⟩
      have hwalk_to_A : ∃ a ∈ A.vertexSet, Nonempty (GraphWalk (sub i).toGraph u₀ a) := by
        rcases hi i with ⟨_, hconn⟩ | ⟨_, hcomp⟩
        · exact ⟨w, hwA, hconn u₀ hu₀i w hwi⟩
        · rcases hcomp u₀ hu₀i with ⟨z, ⟨hzZ, _⟩, hW⟩
          exact ⟨z, hZA hzZ, hW⟩
      rcases hwalk_to_A with ⟨a, haA, ⟨W⟩⟩
      rcases GraphWalk.exists_prefix_in_right_to_sep hsep (hsub i) W hu₀B haA with
        ⟨z', ⟨hz'Z', hz'SB⟩, _⟩
      have hmem : z' ∈ (sub' i).vertexSet ∩ Z' := ⟨hz'SB, hz'Z'⟩
      rw [hdisjZ'] at hmem
      exact hmem
    refine ⟨hA_emp, fun u v ⟨W⟩ => ?_⟩
    -- Every vertex of `sub i` is in `B.vertexSet` and every edge of `sub i` is in `B.edgeSet`.
    have hV_sub_B : (sub i).vertexSet ⊆ B.vertexSet := by
      intro x hxi
      have hxG : x ∈ G.vertexSet := (hsub i).vertexSet_subset hxi
      rw [← hsep.vertexSet_union] at hxG
      rcases hxG with hxA | hxB
      · have h : x ∈ A.vertexSet ∩ (sub i).vertexSet := ⟨hxA, hxi⟩
        rw [hA_emp] at h; exact False.elim h
      · exact hxB
    have h_sub_sub' : (sub i).IsSubdigraph (sub' i) := {
      vertexSet_subset := by rw [hsub'V]; exact subset_inter Subset.rfl hV_sub_B
      edgeSet_subset := fun e he => by
        have heG : e ∈ G.edgeSet := (hsub i).edgeSet_subset he
        have hh_i : G.head e ∈ (sub i).vertexSet := (hsub i).head_eq he ▸ (sub i).head_mem he
        have ht_i : G.tail e ∈ (sub i).vertexSet := (hsub i).tail_eq he ▸ (sub i).tail_mem he
        have heNotA : e ∉ A.edgeSet := by
          intro heA
          have h : G.head e ∈ A.vertexSet ∩ (sub i).vertexSet :=
            ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hh_i⟩
          rw [hA_emp] at h; exact h
        have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
        exact ⟨⟨heG, he, heB⟩, ⟨hh_i, hV_sub_B hh_i⟩, ⟨ht_i, hV_sub_B ht_i⟩⟩
      head_eq := fun e he => (hsub i).head_eq he
      tail_eq := fun e he => (hsub i).tail_eq he
    }
    exact ⟨h_sub_sub'.mapWalk W⟩
  -- Verify `(i)'` for `sub' i`
  have hi' (i : Fin k) : (sub' i).IsConnected ∨
      ((sub' i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub' i).vertexSet, ∃ z' ∈ Z' ∩ (sub' i).vertexSet,
          Nonempty (GraphWalk (sub' i).toGraph u z')) := by
    by_cases hZ'i : ((sub' i).vertexSet ∩ Z').Nonempty
    · right
      rcases hZ'i with ⟨z₀', hz₀'i, hz₀'Z'⟩
      refine ⟨⟨z₀', hz₀'i⟩, fun u hu => ?_⟩
      rw [hsub'V] at hu
      have hwalk_to_A : ∃ a ∈ A.vertexSet, Nonempty (GraphWalk (sub i).toGraph u a) := by
        rcases hi i with ⟨_, hconn⟩ | ⟨_, hcomp⟩
        · rw [hsub'V] at hz₀'i
          exact ⟨z₀', hz₀'Z'.1, hconn u hu.1 z₀' hz₀'i.1⟩
        · rcases hcomp u hu.1 with ⟨z, ⟨hzZ, _⟩, hW⟩
          exact ⟨z, hZA hzZ, hW⟩
      rcases hwalk_to_A with ⟨a, haA, ⟨W⟩⟩
      exact GraphWalk.exists_prefix_in_right_to_sep hsep (hsub i) W hu.2 haA
    · left
      rw [not_nonempty_iff_eq_empty] at hZ'i
      rcases hsub_disj_A_of_disj_Z' i hZ'i with ⟨hA_emp, hwalk_lift⟩
      have hconn_i : (sub i).IsConnected := by
        rcases hi i with hconn | ⟨⟨x₀, hx₀⟩, hcomp⟩
        · exact hconn
        · exfalso
          rcases hcomp x₀ hx₀ with ⟨z, ⟨hzZ, hzi⟩, _⟩
          have h : z ∈ A.vertexSet ∩ (sub i).vertexSet := ⟨hZA hzZ, hzi⟩
          rw [hA_emp] at h; exact h
      refine ⟨by rw [hsub'V]; exact hsub_meets_B i, fun u hu v hv => ?_⟩
      rw [hsub'V] at hu hv
      exact hwalk_lift u v (hconn_i.2 u hu.1 v hv.1)
  -- Verify `(ii)'` for `sub' i, sub' j`
  have hii' (i j : Fin k) (hlt : i < j) :
      (((sub' i).vertexSet ∩ Z').Nonempty ∧ ((sub' j).vertexSet ∩ Z').Nonempty) ∨
        B.HasEdgeBetween (sub' i).vertexSet (sub' j).vertexSet := by
    by_cases h1 : ((sub' i).vertexSet ∩ Z').Nonempty
    · by_cases h2 : ((sub' j).vertexSet ∩ Z').Nonempty
      · exact Or.inl ⟨h1, h2⟩
      · right
        rw [not_nonempty_iff_eq_empty] at h2
        have hA_emp_j := (hsub_disj_A_of_disj_Z' j h2).1
        have hZ_emp_j : ¬ ((sub j).vertexSet ∩ Z).Nonempty := by
          rintro ⟨z, hzj, hzZ⟩
          have h : z ∈ A.vertexSet ∩ (sub j).vertexSet := ⟨hZA hzZ, hzj⟩
          rw [hA_emp_j] at h; exact h
        have hEdge : G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet := by
          rcases hii i j hlt with ⟨_, hZj⟩ | hE
          · exact False.elim (hZ_emp_j hZj)
          · exact hE
        rcases hEdge with ⟨e, heG, h⟩
        have heNotA : e ∉ A.edgeSet := by
          intro heA
          rcases h with ⟨_, htj⟩ | ⟨hhj, _⟩
          · have hm : G.tail e ∈ A.vertexSet ∩ (sub j).vertexSet :=
              ⟨hsep.sub_left.tail_eq heA ▸ A.tail_mem heA, htj⟩
            rw [hA_emp_j] at hm; exact hm
          · have hm : G.head e ∈ A.vertexSet ∩ (sub j).vertexSet :=
              ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hhj⟩
            rw [hA_emp_j] at hm; exact hm
        have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
        refine ⟨e, heB, ?_⟩
        rw [hsub'V, hsub'V, hsep.sub_right.head_eq heB, hsep.sub_right.tail_eq heB]
        have hhB : G.head e ∈ B.vertexSet := hsep.sub_right.head_eq heB ▸ B.head_mem heB
        have htB : G.tail e ∈ B.vertexSet := hsep.sub_right.tail_eq heB ▸ B.tail_mem heB
        rcases h with ⟨hhi, htj⟩ | ⟨hhj, hti⟩
        · exact Or.inl ⟨⟨hhi, hhB⟩, ⟨htj, htB⟩⟩
        · exact Or.inr ⟨⟨hhj, hhB⟩, ⟨hti, htB⟩⟩
    · right
      rw [not_nonempty_iff_eq_empty] at h1
      have hA_emp_i := (hsub_disj_A_of_disj_Z' i h1).1
      have hZ_emp_i : ¬ ((sub i).vertexSet ∩ Z).Nonempty := by
        rintro ⟨z, hzi, hzZ⟩
        have h : z ∈ A.vertexSet ∩ (sub i).vertexSet := ⟨hZA hzZ, hzi⟩
        rw [hA_emp_i] at h; exact h
      have hEdge : G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet := by
        rcases hii i j hlt with ⟨hZi, _⟩ | hE
        · exact False.elim (hZ_emp_i hZi)
        · exact hE
      rcases hEdge with ⟨e, heG, h⟩
      have heNotA : e ∉ A.edgeSet := by
        intro heA
        rcases h with ⟨hhi, _⟩ | ⟨_, hti⟩
        · have hm : G.head e ∈ A.vertexSet ∩ (sub i).vertexSet :=
            ⟨hsep.sub_left.head_eq heA ▸ A.head_mem heA, hhi⟩
          rw [hA_emp_i] at hm; exact hm
        · have hm : G.tail e ∈ A.vertexSet ∩ (sub i).vertexSet :=
            ⟨hsep.sub_left.tail_eq heA ▸ A.tail_mem heA, hti⟩
          rw [hA_emp_i] at hm; exact hm
      have heB : e ∈ B.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_left heNotA
      refine ⟨e, heB, ?_⟩
      rw [hsub'V, hsub'V, hsep.sub_right.head_eq heB, hsep.sub_right.tail_eq heB]
      have hhB : G.head e ∈ B.vertexSet := hsep.sub_right.head_eq heB ▸ B.head_mem heB
      have htB : G.tail e ∈ B.vertexSet := hsep.sub_right.tail_eq heB ▸ B.tail_mem heB
      rcases h with ⟨hhi, htj⟩ | ⟨hhj, hti⟩
      · exact Or.inl ⟨⟨hhi, hhB⟩, ⟨htj, htB⟩⟩
      · exact Or.inr ⟨⟨hhj, hhB⟩, ⟨hti, htB⟩⟩
  -- Verify `(iii)'` for `sub' i`
  have hiii' (i : Fin k) (A' B' : Digraph α β)
      (hsep' : B.IsSeparation A' B') (hZ'A' : Z' ⊆ A'.vertexSet)
      (hnull' : (B.interSub A' (sub' i)).IsNull) :
      ξ ≤ Digraph.separationOrder A' B' := by
    have hA'V_disj : A'.vertexSet ∩ (sub' i).vertexSet = ∅ := by
      have h1 := hnull'.1
      simp only [Digraph.interSub, Digraph.subdigraphOf] at h1
      rw [inter_eq_self_of_subset_right (inter_subset_left.trans hsep'.sub_left.vertexSet_subset)] at h1
      exact h1
    have hZ'_disj : (sub' i).vertexSet ∩ Z' = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxi hxZ'
      have h : x ∈ A'.vertexSet ∩ (sub' i).vertexSet := ⟨hZ'A' hxZ', hxi⟩
      rw [hA'V_disj] at h; exact h
    have hA_emp_i : A.vertexSet ∩ (sub i).vertexSet = ∅ :=
      (hsub_disj_A_of_disj_Z' i hZ'_disj).1
    let A₀ : Digraph α β := G.unionSub A A'
    have hA₀_sub : A₀.IsSubdigraph G := G.subdigraphOf_isSubdigraph _ _
    have hA₀V : A₀.vertexSet = A.vertexSet ∪ A'.vertexSet :=
      inter_eq_self_of_subset_right (union_subset hsep.sub_left.vertexSet_subset
        (hsep'.sub_left.trans hsep.sub_right).vertexSet_subset)
    have hA₀E : A₀.edgeSet = A.edgeSet ∪ A'.edgeSet := by
      have hA'_subG : A'.IsSubdigraph G := hsep'.sub_left.trans hsep.sub_right
      ext e
      simp only [A₀, Digraph.unionSub, Digraph.subdigraphOf, mem_inter_iff, mem_union, mem_ofPred_eq]
      refine ⟨fun h => h.1.2, ?_⟩
      rintro (heA | heA')
      · exact ⟨⟨hsep.sub_left.edgeSet_subset heA, Or.inl heA⟩,
          Or.inl (hsep.sub_left.head_eq heA ▸ A.head_mem heA),
          Or.inl (hsep.sub_left.tail_eq heA ▸ A.tail_mem heA)⟩
      · exact ⟨⟨hA'_subG.edgeSet_subset heA', Or.inr heA'⟩,
          Or.inr (hA'_subG.head_eq heA' ▸ A'.head_mem heA'),
          Or.inr (hA'_subG.tail_eq heA' ▸ A'.tail_mem heA')⟩
    have hsep₀ : G.IsSeparation A₀ B' := {
      sub_left := hA₀_sub
      sub_right := hsep'.sub_right.trans hsep.sub_right
      vertexSet_union := by rw [hA₀V, union_assoc, hsep'.vertexSet_union, hsep.vertexSet_union]
      edgeSet_union := by rw [hA₀E, union_assoc, hsep'.edgeSet_union, hsep.edgeSet_union]
      edgeSet_disjoint := by
        rw [hA₀E, disjoint_union_left]
        exact ⟨hsep.edgeSet_disjoint.mono_right hsep'.sub_right.edgeSet_subset, hsep'.edgeSet_disjoint⟩
    }
    have hZA₀ : Z ⊆ A₀.vertexSet := by rw [hA₀V]; exact hZA.trans subset_union_left
    have hA₀V_disj : A₀.vertexSet ∩ (sub i).vertexSet = ∅ := by
      rw [hA₀V]
      ext x
      simp only [mem_inter_iff, mem_union, mem_empty_iff_false, iff_false, not_and]
      rintro (hxA | hxA') hxi
      · have h : x ∈ A.vertexSet ∩ (sub i).vertexSet := ⟨hxA, hxi⟩
        rw [hA_emp_i] at h; exact h
      · have h : x ∈ A'.vertexSet ∩ (sub' i).vertexSet := by
          rw [hsub'V]
          exact ⟨hxA', hxi, hsep'.sub_left.vertexSet_subset hxA'⟩
        rw [hA'V_disj] at h; exact h
    have hnull₀ : (G.interSub A₀ (sub i)).IsNull := by
      refine ⟨?_, ?_⟩
      · simp only [Digraph.interSub, Digraph.subdigraphOf]
        rw [inter_eq_self_of_subset_right (inter_subset_left.trans hA₀_sub.vertexSet_subset)]
        exact hA₀V_disj
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        have hh : G.head e ∈ A₀.vertexSet ∩ (sub i).vertexSet := h.2.1
        rw [hA₀V_disj] at hh; exact hh
    have hord := hiii i A₀ B' hsep₀ hZA₀ hnull₀
    have hA₀B'_eq : A₀.vertexSet ∩ B'.vertexSet = A'.vertexSet ∩ B'.vertexSet := by
      rw [hA₀V]
      ext x
      simp only [mem_inter_iff, mem_union]
      refine ⟨fun ⟨h, hxB'⟩ => ⟨?_, hxB'⟩, fun ⟨hxA', hxB'⟩ => ⟨Or.inr hxA', hxB'⟩⟩
      rcases h with hxA | hxA'
      · exact hZ'A' ⟨hxA, hsep'.sub_right.vertexSet_subset hxB'⟩
      · exact hxA'
    unfold Digraph.separationOrder at hord ⊢
    rw [hA₀B'_eq] at hord
    exact hord
  -- Apply `ih` to `(B, Z', sub')`
  obtain ⟨μ, hμ, H', hH'_sub, hH'_conn, hH'_disj, hH'_a, hH'_b⟩ :=
    ih Z' sub' hBfin inter_subset_right hZ'card hsub'_sub hdisj' hi' hii' hiii'
  -- Step 2: Apply Menger's theorem in `A` between `Z` and `Z'`
  let K : SimpleGraph ↥A.vertexSet := {
    Adj u v := u ≠ v ∧ A.toGraph.Adj u.1 v.1
    symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  let X₀ : Set ↥A.vertexSet := {u : ↥A.vertexSet | u.1 ∈ Z}
  let Y₀ : Set ↥A.vertexSet := {u : ↥A.vertexSet | u.1 ∈ Z'}
  have hAfin_sub : Finite ↥A.vertexSet := hAfin.finite_V.to_subtype
  -- Verify the separator condition for `GraphMinor.Menger.exists_disjointPaths`
  have hMenger_cond : ∀ S₀ : Set ↥A.vertexSet,
      (∀ P : PathFromTo K X₀ Y₀, ∃ x ∈ P.walk.support, x ∈ S₀) → ξ ≤ S₀.ncard := by
    intro S₀ hS₀_sep
    let S : Set α := Subtype.val '' S₀
    have hS_sub_A : S ⊆ A.vertexSet := by rintro _ ⟨u, _, rfl⟩; exact u.2
    have hS_card : S.ncard = S₀.ncard := ncard_image_of_injective S₀ Subtype.val_injective
    let R : Set α := {v : α | ∃ (hvA : v ∈ A.vertexSet) (z : ↥A.vertexSet),
      z.1 ∈ Z ∧ ∃ w : K.Walk z ⟨v, hvA⟩, ∀ u ∈ w.support, u.1 ∉ S}
    have hR_sub_A : R ⊆ A.vertexSet \ S := by
      rintro v ⟨hvA, z, _, w, hw⟩
      exact ⟨hvA, hw ⟨v, hvA⟩ (SimpleGraph.Walk.end_mem_support w)⟩
    have hR_disj_Z' : R ∩ Z' = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨hvA, z, hzZ, w, hw⟩ hvZ'
      let p : PathFromTo K X₀ Y₀ := ⟨z, ⟨v, hvA⟩, w.bypass, w.bypass_isPath, hzZ, hvZ'⟩
      obtain ⟨u, hu_supp, huS₀⟩ := hS₀_sep p
      exact hw u (w.support_bypass_subset_support hu_supp) ⟨u, huS₀, rfl⟩
    have hR_disj_B : R ∩ B.vertexSet = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hvR hvB
      have hvZ' : v ∈ R ∩ Z' := ⟨hvR, (hR_sub_A hvR).1, hvB⟩
      rw [hR_disj_Z'] at hvZ'; exact hvZ'
    let VA₁ : Set α := R ∪ S
    let EA₁ : Set β := {e ∈ A.edgeSet | G.head e ∈ VA₁ ∧ G.tail e ∈ VA₁}
    let VB₁ : Set α := G.vertexSet \ R
    let EB₁ : Set β := G.edgeSet \ EA₁
    let A₁ : Digraph α β := G.subdigraphOf VA₁ EA₁
    let B₁ : Digraph α β := G.subdigraphOf VB₁ EB₁
    have hVA₁_sub_A : VA₁ ⊆ A.vertexSet :=
      union_subset (hR_sub_A.trans sdiff_subset) hS_sub_A
    have hA₁V : A₁.vertexSet = VA₁ :=
      inter_eq_self_of_subset_right (hVA₁_sub_A.trans hsep.sub_left.vertexSet_subset)
    have hB₁V : B₁.vertexSet = VB₁ :=
      inter_eq_self_of_subset_right sdiff_subset
    have hA₁E : A₁.edgeSet = EA₁ := by
      ext e
      simp only [A₁, EA₁, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1.2, fun ⟨heA, hh, ht⟩ =>
        ⟨⟨hsep.sub_left.edgeSet_subset heA, heA, hh, ht⟩, hh, ht⟩⟩
    have hR_step : ∀ {u v : α} (huR : u ∈ R) (hvA : v ∈ A.vertexSet)
        (hadj : A.toGraph.Adj u v) (hvNotS : v ∉ S), v ∈ R := by
      intro u v huR hvA hadj hvNotS
      by_cases huv : u = v
      · exact huv ▸ huR
      · rcases huR with ⟨huA, z, hzZ, w, hw⟩
        have hadjK : K.Adj ⟨u, huA⟩ ⟨v, hvA⟩ := ⟨fun h => huv (congrArg Subtype.val h), hadj⟩
        refine ⟨hvA, z, hzZ, w.concat hadjK, fun q hq => ?_⟩
        simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at hq
        rcases hq with hq | rfl
        · exact hw q hq
        · exact hvNotS
    -- Every edge in `EB₁ = G.edgeSet \ EA₁` has neither end in `R`.
    have hEB₁_no_R (e : β) (heG : e ∈ G.edgeSet) (heNotEA₁ : e ∉ EA₁) :
        G.head e ∉ R ∧ G.tail e ∉ R := by
      by_cases heB : e ∈ B.edgeSet
      · have hhB : G.head e ∈ B.vertexSet := hsep.sub_right.head_eq heB ▸ B.head_mem heB
        have htB : G.tail e ∈ B.vertexSet := hsep.sub_right.tail_eq heB ▸ B.tail_mem heB
        refine ⟨fun hhR => ?_, fun htR => ?_⟩
        · have h : G.head e ∈ R ∩ B.vertexSet := ⟨hhR, hhB⟩
          rw [hR_disj_B] at h; exact h
        · have h : G.tail e ∈ R ∩ B.vertexSet := ⟨htR, htB⟩
          rw [hR_disj_B] at h; exact h
      · have heA : e ∈ A.edgeSet := (hsep.edgeSet_union ▸ heG).resolve_right heB
        have hhA : G.head e ∈ A.vertexSet := hsep.sub_left.head_eq heA ▸ A.head_mem heA
        have htA : G.tail e ∈ A.vertexSet := hsep.sub_left.tail_eq heA ▸ A.tail_mem heA
        have hadj_ht : A.toGraph.Adj (G.head e) (G.tail e) :=
          ⟨e, heA, Or.inl ⟨hsep.sub_left.head_eq heA, hsep.sub_left.tail_eq heA⟩⟩
        refine ⟨fun hhR => heNotEA₁ ⟨heA, Or.inl hhR, ?_⟩,
          fun htR => heNotEA₁ ⟨heA, ?_, Or.inl htR⟩⟩
        · by_cases htS : G.tail e ∈ S
          · exact Or.inr htS
          · exact Or.inl (hR_step hhR htA hadj_ht htS)
        · by_cases hhS : G.head e ∈ S
          · exact Or.inr hhS
          · exact Or.inl (hR_step htR hhA hadj_ht.symm hhS)
    have hB₁E : B₁.edgeSet = EB₁ := by
      ext e
      simp only [B₁, EB₁, VB₁, Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_ofPred_eq]
      refine ⟨fun h => h.1.2, fun ⟨heG, heNot⟩ => ?_⟩
      have hnoR := hEB₁_no_R e heG heNot
      exact ⟨⟨heG, heG, heNot⟩, ⟨G.head_mem heG, hnoR.1⟩, ⟨G.tail_mem heG, hnoR.2⟩⟩
    have hsep₁ : G.IsSeparation A₁ B₁ := {
      sub_left := G.subdigraphOf_isSubdigraph _ _
      sub_right := G.subdigraphOf_isSubdigraph _ _
      vertexSet_union := by
        rw [hA₁V, hB₁V]
        ext x
        simp only [VA₁, VB₁, mem_union, mem_sdiff]
        exact ⟨fun h => h.elim (fun h1 => hsep.sub_left.vertexSet_subset (hVA₁_sub_A h1)) (fun h2 => h2.1),
          fun hxG => if hxR : x ∈ R then Or.inl (Or.inl hxR) else Or.inr ⟨hxG, hxR⟩⟩
      edgeSet_union := by
        rw [hA₁E, hB₁E]
        ext e
        simp only [mem_union]
        exact ⟨fun h => h.elim (fun heEA₁ => hsep.sub_left.edgeSet_subset heEA₁.1) (fun h2 => h2.1),
          fun heG => if heEA₁ : e ∈ EA₁ then Or.inl heEA₁ else Or.inr ⟨heG, heEA₁⟩⟩
      edgeSet_disjoint := by
        rw [hA₁E, hB₁E]
        exact disjoint_sdiff_right
    }
    have hZA₁ : Z ⊆ A₁.vertexSet := by
      rw [hA₁V]
      intro z hz
      by_cases hzS : z ∈ S
      · exact Or.inr hzS
      · refine Or.inl ⟨hZA hz, ⟨z, hZA hz⟩, hz, .nil, fun u hu => ?_⟩
        simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hu
        exact hu ▸ hzS
    have hA₁V_disj : A₁.vertexSet ∩ (sub i₁).vertexSet = ∅ := by
      rw [hA₁V]
      ext x
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hxVA₁ hxi₁
      have h : x ∈ A.vertexSet ∩ (sub i₁).vertexSet := ⟨hVA₁_sub_A hxVA₁, hxi₁⟩
      rw [hi₁A_emp] at h; exact h
    have hnull₁ : (G.interSub A₁ (sub i₁)).IsNull := by
      refine ⟨?_, ?_⟩
      · simp only [Digraph.interSub, Digraph.subdigraphOf]
        rw [inter_eq_self_of_subset_right (inter_subset_left.trans (G.subdigraphOf_isSubdigraph _ _).vertexSet_subset)]
        exact hA₁V_disj
      · ext e
        simp only [Digraph.interSub, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq,
          mem_empty_iff_false, iff_false]
        intro h
        have hh : G.head e ∈ A₁.vertexSet ∩ (sub i₁).vertexSet := h.2.1
        rw [hA₁V_disj] at hh; exact hh
    have hord₁ := hiii i₁ A₁ B₁ hsep₁ hZA₁ hnull₁
    have hA₁B₁_eq : A₁.vertexSet ∩ B₁.vertexSet = S := by
      rw [hA₁V, hB₁V]
      ext x
      simp only [VA₁, VB₁, mem_inter_iff, mem_union, mem_sdiff]
      constructor
      · rintro ⟨hxR | hxS, _, hxNotR⟩
        · exact False.elim (hxNotR hxR)
        · exact hxS
      · intro hxS
        exact ⟨Or.inr hxS, hsep.sub_left.vertexSet_subset (hS_sub_A hxS),
          fun hxR => (hR_sub_A hxR).2 hxS⟩
    unfold Digraph.separationOrder at hord₁
    rw [hA₁B₁_eq, hS_card] at hord₁
    exact hord₁
  obtain ⟨P₀, hP₀_disj⟩ :=
    GraphMinor.Menger.exists_disjointPaths K X₀ Y₀ hAfin_sub ξ hMenger_cond
  -- Properties of the `ξ` vertex-disjoint paths `P₀ r` (`r : Fin ξ`) in `A`
  let VP (r : Fin ξ) : Set α := {x ∈ A.vertexSet | ∃ u ∈ (P₀ r).walk.support, u.1 = x}
  let z_start (r : Fin ξ) : α := (P₀ r).first.1
  let z'_end (r : Fin ξ) : α := (P₀ r).last.1
  have hVP_sub_A (r : Fin ξ) : VP r ⊆ A.vertexSet := sep_subset _ _
  have hVP_disj : Pairwise (fun r₁ r₂ : Fin ξ => Disjoint (VP r₁) (VP r₂)) := by
    intro r₁ r₂ hne
    rw [Set.disjoint_iff]
    rintro x ⟨⟨_, u₁, hu₁, rfl⟩, ⟨_, u₂, hu₂, hu_eq⟩⟩
    have hu₁₂ : u₁ = u₂ := Subtype.ext hu_eq.symm
    exact Set.disjoint_left.mp (hP₀_disj hne) hu₁ (hu₁₂ ▸ hu₂)
  have hz_start_mem (r : Fin ξ) : z_start r ∈ VP r ∩ Z :=
    ⟨⟨(P₀ r).first.2, (P₀ r).first, SimpleGraph.Walk.start_mem_support _, rfl⟩, (P₀ r).first_mem⟩
  have hz'_end_mem (r : Fin ξ) : z'_end r ∈ VP r ∩ Z' :=
    ⟨⟨(P₀ r).last.2, (P₀ r).last, SimpleGraph.Walk.end_mem_support _, rfl⟩, (P₀ r).last_mem⟩
  have hz_start_inj : Function.Injective z_start := by
    intro r₁ r₂ heq
    by_contra hne
    exact Set.disjoint_left.mp (hVP_disj hne) (hz_start_mem r₁).1 (heq ▸ (hz_start_mem r₂).1)
  have hz'_end_inj : Function.Injective z'_end := by
    intro r₁ r₂ heq
    by_contra hne
    exact Set.disjoint_left.mp (hVP_disj hne) (hz'_end_mem r₁).1 (heq ▸ (hz'_end_mem r₂).1)
  have hrange_z_start : Set.range z_start = Z := by
    apply eq_of_subset_of_ncard_le
    · rintro _ ⟨r, rfl⟩; exact (hz_start_mem r).2
    · rw [ncard_range_of_injective hz_start_inj, Nat.card_fin, hZcard]
    · exact hZfin
  have hrange_z'_end : Set.range z'_end = Z' := by
    apply eq_of_subset_of_ncard_le
    · rintro _ ⟨r, rfl⟩; exact (hz'_end_mem r).2
    · rw [ncard_range_of_injective hz'_end_inj, Nat.card_fin, hZ'card]
    · exact hZ'fin
  have hVP_inter_Z (r : Fin ξ) : VP r ∩ Z = {z_start r} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxVP, hxZ⟩ => ?_, fun h => h.symm ▸ hz_start_mem r⟩
    rw [← hrange_z_start] at hxZ
    rcases hxZ with ⟨r', rfl⟩
    have hrr' : r = r' := by
      by_contra hne
      exact Set.disjoint_left.mp (hVP_disj hne) hxVP (hz_start_mem r').1
    rw [hrr']
  have hVP_inter_Z' (r : Fin ξ) : VP r ∩ Z' = {z'_end r} := by
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hxVP, hxZ'⟩ => ?_, fun h => h.symm ▸ hz'_end_mem r⟩
    rw [← hrange_z'_end] at hxZ'
    rcases hxZ' with ⟨r', rfl⟩
    have hrr' : r = r' := by
      by_contra hne
      exact Set.disjoint_left.mp (hVP_disj hne) hxVP (hz'_end_mem r').1
    rw [hrr']
  -- Match each `i < ξ` to the unique `r : Fin ξ` with `z'_end r ∈ (H' i).vertexSet ∩ Z'`
  have hex_r (i : Fin (k - (ξ - μ) / 2)) (hi_lt : i.1 < ξ) :
      ∃ r : Fin ξ, (H' i).vertexSet ∩ Z' = {z'_end r} := by
    have hcard1 := (hH'_a i).1 hi_lt
    rcases ncard_eq_one.mp hcard1 with ⟨w, hw⟩
    have hw_mem : w ∈ (H' i).vertexSet ∩ Z' := hw ▸ mem_singleton w
    have hwZ' : w ∈ Z' := hw_mem.2
    rw [← hrange_z'_end] at hwZ'
    rcases hwZ' with ⟨r, rfl⟩
    exact ⟨r, hw⟩
  let rOf (i : Fin (k - (ξ - μ) / 2)) (hi_lt : i.1 < ξ) : Fin ξ :=
    Classical.choose (hex_r i hi_lt)
  have hrOf_spec (i : Fin (k - (ξ - μ) / 2)) (hi_lt : i.1 < ξ) :
      (H' i).vertexSet ∩ Z' = {z'_end (rOf i hi_lt)} :=
    Classical.choose_spec (hex_r i hi_lt)
  have hrOf_inj : ∀ ⦃i j : Fin (k - (ξ - μ) / 2)⦄ (hi_lt : i.1 < ξ) (hj_lt : j.1 < ξ),
      rOf i hi_lt = rOf j hj_lt → i = j := by
    intro i j hi_lt hj_lt heq
    by_contra hij
    have hm₁ : z'_end (rOf i hi_lt) ∈ (H' i).vertexSet ∩ Z' := by
      rw [hrOf_spec i hi_lt]; exact mem_singleton _
    have hm₂ : z'_end (rOf i hi_lt) ∈ (H' j).vertexSet ∩ Z' := by
      rw [heq, hrOf_spec j hj_lt]; exact mem_singleton _
    exact Set.disjoint_left.mp (hH'_disj hij) hm₁.1 hm₂.1
  -- Define `H : Fin (k - (ξ - μ) / 2) → Digraph α β`
  let H (i : Fin (k - (ξ - μ) / 2)) : Digraph α β :=
    if hi_lt : i.1 < ξ then
      let r := rOf i hi_lt
      G.subdigraphOf (VP r ∪ (H' i).vertexSet) ((A.induce (VP r)).edgeSet ∪ (H' i).edgeSet)
    else
      H' i
  have hHV_lt (i : Fin (k - (ξ - μ) / 2)) (hi_lt : i.1 < ξ) :
      (H i).vertexSet = VP (rOf i hi_lt) ∪ (H' i).vertexSet := by
    dsimp [H]
    simp only [hi_lt, ↓reduceDIte]
    exact inter_eq_self_of_subset_right (union_subset
      ((hVP_sub_A _).trans hsep.sub_left.vertexSet_subset)
      ((hH'_sub i).trans hsep.sub_right).vertexSet_subset)
  have hHE_lt (i : Fin (k - (ξ - μ) / 2)) (hi_lt : i.1 < ξ) :
      (H i).edgeSet = (A.induce (VP (rOf i hi_lt))).edgeSet ∪ (H' i).edgeSet := by
    let r := rOf i hi_lt
    dsimp [H]
    simp only [hi_lt, ↓reduceDIte]
    ext e
    simp only [Digraph.subdigraphOf, mem_inter_iff, mem_union, mem_ofPred_eq]
    refine ⟨fun h => h.1.2, ?_⟩
    rintro (heP | heH')
    · have heA : e ∈ A.edgeSet := heP.1
      have heG : e ∈ G.edgeSet := hsep.sub_left.edgeSet_subset heA
      have hh : G.head e ∈ VP r := hsep.sub_left.head_eq heA ▸ heP.2.1
      have ht : G.tail e ∈ VP r := hsep.sub_left.tail_eq heA ▸ heP.2.2
      exact ⟨⟨heG, Or.inl heP⟩, Or.inl hh, Or.inl ht⟩
    · have heB : e ∈ B.edgeSet := (hH'_sub i).edgeSet_subset heH'
      have heG : e ∈ G.edgeSet := hsep.sub_right.edgeSet_subset heB
      have hh : G.head e ∈ (H' i).vertexSet :=
        hsep.sub_right.head_eq heB ▸ (hH'_sub i).head_eq heH' ▸ (H' i).head_mem heH'
      have ht : G.tail e ∈ (H' i).vertexSet :=
        hsep.sub_right.tail_eq heB ▸ (hH'_sub i).tail_eq heH' ▸ (H' i).tail_mem heH'
      exact ⟨⟨heG, Or.inr heH'⟩, Or.inr hh, Or.inr ht⟩
  have hH_disj : Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) := by
    intro i j hij
    -- Note that for any `r : Fin ξ`, `VP r ∩ B.vertexSet = VP r ∩ Z' = {z'_end r}`
    have hVP_inter_B (r : Fin ξ) : VP r ∩ B.vertexSet = {z'_end r} := by
      have h : VP r ∩ B.vertexSet = VP r ∩ Z' := by
        ext x
        simp only [Z', mem_inter_iff]
        exact ⟨fun ⟨hxVP, hxB⟩ => ⟨hxVP, hVP_sub_A r hxVP, hxB⟩,
          fun ⟨hxVP, _, hxB⟩ => ⟨hxVP, hxB⟩⟩
      rw [h, hVP_inter_Z']
    -- Thus for `hi_lt : i.1 < ξ`, `(H i).vertexSet ∩ B.vertexSet = (H' i).vertexSet`
    -- and `(H i).vertexSet \ B.vertexSet = VP (rOf i hi_lt) \ B.vertexSet`
    have hH_decomp (m : Fin (k - (ξ - μ) / 2)) :
        (H m).vertexSet ∩ B.vertexSet = (H' m).vertexSet ∧
        (∀ hm_ge : ¬ m.1 < ξ, (H m).vertexSet ⊆ B.vertexSet) ∧
        (∀ hm_lt : m.1 < ξ, (H m).vertexSet \ B.vertexSet ⊆ VP (rOf m hm_lt)) := by
      refine ⟨?_, ?_, ?_⟩
      · by_cases hm_lt : m.1 < ξ
        · rw [hHV_lt m hm_lt, union_inter_distrib_right, hVP_inter_B,
            inter_eq_self_of_subset_left (hH'_sub m).vertexSet_subset]
          have hz'_mem : z'_end (rOf m hm_lt) ∈ (H' m).vertexSet := by
            have h := hrOf_spec m hm_lt
            have hm' : z'_end (rOf m hm_lt) ∈ (H' m).vertexSet ∩ Z' := h ▸ mem_singleton _
            exact hm'.1
          exact union_eq_self_of_subset_left (singleton_subset_iff.mpr hz'_mem)
        · dsimp [H]
          simp only [hm_lt, ↓reduceDIte]
          exact inter_eq_self_of_subset_left (hH'_sub m).vertexSet_subset
      · intro hm_ge
        dsimp [H]
        simp only [hm_ge, ↓reduceDIte]
        exact (hH'_sub m).vertexSet_subset
      · intro hm_lt
        rw [hHV_lt m hm_lt]
        rintro x ⟨hxVP | hxH', hxNotB⟩
        · exact hxVP
        · exact False.elim (hxNotB ((hH'_sub m).vertexSet_subset hxH'))
    rw [Set.disjoint_iff]
    rintro x ⟨hxi, hxj⟩
    by_cases hxB : x ∈ B.vertexSet
    · have hxi' : x ∈ (H' i).vertexSet := (hH_decomp i).1 ▸ ⟨hxi, hxB⟩
      have hxj' : x ∈ (H' j).vertexSet := (hH_decomp j).1 ▸ ⟨hxj, hxB⟩
      exact Set.disjoint_left.mp (hH'_disj hij) hxi' hxj'
    · by_cases hi_lt : i.1 < ξ
      · by_cases hj_lt : j.1 < ξ
        · have hxPi : x ∈ VP (rOf i hi_lt) := (hH_decomp i).2.2 hi_lt ⟨hxi, hxB⟩
          have hxPj : x ∈ VP (rOf j hj_lt) := (hH_decomp j).2.2 hj_lt ⟨hxj, hxB⟩
          have hne_r : rOf i hi_lt ≠ rOf j hj_lt := fun h => hij (hrOf_inj hi_lt hj_lt h)
          exact Set.disjoint_left.mp (hVP_disj hne_r) hxPi hxPj
        · exact hxB ((hH_decomp j).2.1 hj_lt hxj)
      · exact hxB ((hH_decomp i).2.1 hi_lt hxi)
  refine ⟨μ, hμ, H, ?_, ?_, hH_disj, ?_, ?_⟩
  · -- `IsSubdigraph`
    intro i
    dsimp [H]
    split_ifs with hi_lt
    · exact G.subdigraphOf_isSubdigraph _ _
    · exact (hH'_sub i).trans hsep.sub_right
  · -- `IsConnected`
    intro i
    by_cases hi_lt : i.1 < ξ
    · let r := rOf i hi_lt
      have hHV := hHV_lt i hi_lt
      have hHE := hHE_lt i hi_lt
      -- Every vertex in `VP r` has a walk in `H i` to `z'_end r`.
      have hwalk_K : ∀ {u v : ↥A.vertexSet} (w : K.Walk u v),
          (∀ q ∈ w.support, q.1 ∈ VP r) →
          Nonempty (GraphWalk (H i).toGraph u.1 v.1) := by
        intro u v w hsupp
        induction w with
        | @nil u =>
          have huVP : u.1 ∈ VP r := hsupp u (SimpleGraph.Walk.start_mem_support _)
          have huHi : u.1 ∈ (H i).vertexSet := hHV.symm ▸ Or.inl huVP
          exact ⟨.nil huHi⟩
        | @cons u v w hadj rest ih_w =>
          rcases ih_w (fun q hq => hsupp q (List.mem_cons_of_mem _ hq)) with ⟨W'⟩
          have huVP : u.1 ∈ VP r := hsupp u List.mem_cons_self
          have hvVP : v.1 ∈ VP r := hsupp v (List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support _))
          rcases hadj.2 with ⟨e, heA, hlinkA⟩
          have heP : e ∈ (A.induce (VP r)).edgeSet := by
            refine ⟨heA, ?_⟩
            rcases hlinkA with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1.symm ▸ huVP, h2.symm ▸ hvVP⟩
            · exact ⟨h1.symm ▸ hvVP, h2.symm ▸ huVP⟩
          have heHi : e ∈ (H i).edgeSet := hHE.symm ▸ Or.inl heP
          have hlinkHi : (H i).toGraph.IsLink e u.1 v.1 := by
            refine ⟨heHi, ?_⟩
            dsimp [H]
            simp only [hi_lt, ↓reduceDIte]
            change (G.head e = u.1 ∧ G.tail e = v.1) ∨ (G.head e = v.1 ∧ G.tail e = u.1)
            rw [← hsep.sub_left.head_eq heA, ← hsep.sub_left.tail_eq heA]
            exact hlinkA
          exact ⟨.cons hlinkHi W'⟩
      have hH'_sub_Hi : (H' i).IsSubdigraph (H i) := {
        vertexSet_subset := by rw [hHV]; exact subset_union_right
        edgeSet_subset := by rw [hHE]; exact subset_union_right
        head_eq := fun e he => by
          dsimp [H]; simp only [hi_lt, ↓reduceDIte]
          exact ((hH'_sub i).trans hsep.sub_right).head_eq he
        tail_eq := fun e he => by
          dsimp [H]; simp only [hi_lt, ↓reduceDIte]
          exact ((hH'_sub i).trans hsep.sub_right).tail_eq he
      }
      have hz'_in_H' : z'_end r ∈ (H' i).vertexSet := by
        have h := hrOf_spec i hi_lt
        have hm : z'_end r ∈ (H' i).vertexSet ∩ Z' := h ▸ mem_singleton _
        exact hm.1
      have hwalk_to_z' (x : α) (hx : x ∈ (H i).vertexSet) :
          Nonempty (GraphWalk (H i).toGraph x (z'_end r)) := by
        rw [hHV] at hx
        rcases hx with hxVP | hxH'
        · rcases hxVP with ⟨hxA, u, hu_supp, rfl⟩
          let w_uz' := (P₀ r).walk.dropUntil u hu_supp
          have hsupp_sub : ∀ q ∈ w_uz'.support, q.1 ∈ VP r := by
            intro q hq
            exact ⟨q.2, q, SimpleGraph.Walk.support_dropUntil_subset_support (P₀ r).walk hu_supp hq, rfl⟩
          exact hwalk_K w_uz' hsupp_sub
        · rcases (hH'_conn i).2 x hxH' (z'_end r) hz'_in_H' with ⟨W'⟩
          exact ⟨hH'_sub_Hi.mapWalk W'⟩
      refine ⟨⟨z'_end r, hHV.symm ▸ Or.inr hz'_in_H'⟩, fun x hx y hy => ?_⟩
      rcases hwalk_to_z' x hx with ⟨Wx⟩
      rcases hwalk_to_z' y hy with ⟨Wy⟩
      exact ⟨GraphWalk.append Wx (GraphWalk.reverse Wy)⟩
    · dsimp [H]
      simp only [hi_lt, ↓reduceDIte]
      exact hH'_conn i
  · -- Condition (a)
    intro i
    have hH'Z_sub (m : Fin (k - (ξ - μ) / 2)) :
        (H' m).vertexSet ∩ Z ⊆ (H' m).vertexSet ∩ Z' := by
      rintro x ⟨hxH', hxZ⟩
      exact ⟨hxH', hZA hxZ, (hH'_sub m).vertexSet_subset hxH'⟩
    constructor
    · intro hi_lt
      let r := rOf i hi_lt
      rw [hHV_lt i hi_lt, union_inter_distrib_right]
      have hsub_VP : (H' i).vertexSet ∩ Z ⊆ VP r ∩ Z := by
        intro x hx
        have hx' : x ∈ (H' i).vertexSet ∩ Z' := hH'Z_sub i hx
        rw [hrOf_spec i hi_lt, mem_singleton_iff] at hx'
        exact ⟨hx' ▸ (hz'_end_mem r).1, hx.2⟩
      rw [union_eq_self_of_subset_right hsub_VP, hVP_inter_Z r, ncard_singleton]
    · intro hi_ge
      have hnot_lt : ¬ i.1 < ξ := by omega
      dsimp [H]
      simp only [hnot_lt, ↓reduceDIte]
      have hZ'_emp := (hH'_a i).2 hi_ge
      exact subset_eq_empty (hH'Z_sub i) hZ'_emp
  · -- Condition (b)
    intro i j hlt hnoEdge
    apply hH'_b i j hlt
    rintro ⟨e, heB, h⟩
    apply hnoEdge
    have hsub_V (m : Fin (k - (ξ - μ) / 2)) : (H' m).vertexSet ⊆ (H m).vertexSet := by
      by_cases hm_lt : m.1 < ξ
      · rw [hHV_lt m hm_lt]; exact subset_union_right
      · dsimp [H]; simp only [hm_lt, ↓reduceDIte]; exact Subset.rfl
    refine ⟨e, hsep.sub_right.edgeSet_subset heB, ?_⟩
    rw [← hsep.sub_right.head_eq heB, ← hsep.sub_right.tail_eq heB]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hsub_V i h1, hsub_V j h2⟩
    · exact Or.inr ⟨hsub_V j h1, hsub_V i h2⟩

end GraphMinor.GM13
