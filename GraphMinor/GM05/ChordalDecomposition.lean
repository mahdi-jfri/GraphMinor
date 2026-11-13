module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.Simplicial
import GraphMinor.GM05.ForestDecomposition
import GraphMinor.GM05.TreeHelly

/-!
# Clique bags for chordal graphs

Delete a simplicial vertex using Graph Minors V, (8.4). Its neighbors form
a clique, so their subtrees in the smaller decomposition meet at one tree
vertex by tree Helly. Attach a leaf with the deleted vertex and its
neighbors as its bag. Every bag remains a clique. This constructs the
representation required for the reverse direction of (8.3).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

universe u

private def delete_embedding {V : Type*} (G : (⊤ : SimpleGraph V).Subgraph) (S : Set V) :
    (G.deleteVerts S).coe ↪g G.coe where
  toFun x := ⟨x.1,x.2.1⟩
  inj' _ _ h := Subtype.ext (congrArg (fun z : G.verts ↦ z.val) h)
  map_rel_iff' := by
    intro x y
    change G.Adj x.1 y.1 ↔ (G.deleteVerts S).Adj x.1 y.1
    exact ⟨fun h ↦ ⟨x.2,y.2,h⟩,fun h ↦ h.2.2⟩

/-- From Graph Minors V, (8.4), a finite chordal graph has a
tree-decomposition all of whose bags are cliques. -/
theorem chordal_clique_decomposition
    {V : Type u} {G : (⊤ : SimpleGraph V).Subgraph}
    (hfin : G.verts.Finite) (hG : IsChordal G.coe) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (χ : ι → Set V),
      IsTreeDecomposition G T χ ∧ ∀ t, (χ t).Pairwise G.Adj := by
  classical
  have main : ∀ n, ∀ G : (⊤ : SimpleGraph V).Subgraph,
      G.verts.Finite → G.verts.ncard=n → IsChordal G.coe →
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (χ : ι → Set V),
        IsTreeDecomposition G T χ ∧ ∀ t, (χ t).Pairwise G.Adj := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hfin hcard hG
      by_cases hne : G.verts.Nonempty
      swap
      · have he : G.verts=∅ := not_nonempty_iff_eq_empty.mp hne
        refine ⟨Fin 1,inferInstance,⊥,fun _ ↦ ∅,?_,fun _ ↦ by simp⟩
        refine ⟨?_,?_,?_,?_⟩
        · exact IsTree.of_subsingleton
        · simp [he]
        · intro x y hxy
          exact (hne ⟨x,hxy.fst_mem⟩).elim
        · intro a t b hp x hx
          exact hx.1
      let : Finite G.verts := hfin.to_subtype
      let : Nonempty G.verts := hne.to_subtype
      obtain ⟨v,hv⟩ := theorem_8_4_proof G.coe hG
      let D := G.deleteVerts {v.1}
      have hDfin : D.verts.Finite := hfin.subset sdiff_subset
      have hDcard : D.verts.ncard<n := by
        rw [←hcard]
        exact ncard_sdiff_singleton_lt_of_mem v.2 hfin
      have hD : IsChordal D.coe := hG.of_embedding (delete_embedding G {v.1})
      obtain ⟨ι,inst,T,χ,htd,hclique⟩ := ih _ hDcard D hDfin rfl hD
      let := inst
      let B : Set V := {x | G.Adj v.1 x}
      have hBN : ∀ x ∈ B, x≠v.1 := fun x hx ↦ hx.ne.symm
      have hBclique : B.Pairwise G.Adj := by
        intro x hx y hy hxy
        apply hv (x:=⟨x,hx.snd_mem⟩) (y:=⟨y,hy.snd_mem⟩) hx hy
        intro he
        exact hxy (congrArg (fun z : G.verts ↦ z.val) he)
      let A (x : B) : Set ι := {t | x.1 ∈ χ t}
      have hcover : (⋃ t,χ t)=D.verts := htd.iUnion_eq
      have hpair : ∀ x y : B, (A x ∩ A y).Nonempty := by
        intro x y
        by_cases he : x.1=y.1
        · have hxD : x.1 ∈ D.verts := ⟨x.2.snd_mem,hBN x.1 x.2⟩
          rw [←hcover] at hxD
          obtain ⟨t,ht⟩ := mem_iUnion.mp hxD
          refine ⟨t,ht,?_⟩
          change y.1 ∈ χ t
          rw [←he]
          exact ht
        · have hxy : D.Adj x.1 y.1 :=
            ⟨⟨x.2.snd_mem,hBN x.1 x.2⟩,⟨y.2.snd_mem,hBN y.1 y.2⟩,hBclique x.2 y.2 he⟩
          exact htd.adj_mem hxy
      have hconv : ∀ x a, a∈A x → ∀ b, b∈A x → ∀ c,
          OnTreePath T a b c → c∈A x := by
        intro x a ha b hb c hp
        exact htd.inter_subset hp ⟨ha,hb⟩
      obtain ⟨t₀,ht₀⟩ := tree_helly htd.isTree A hconv hpair
      have hB : B⊆χ t₀ := fun x hx ↦ ht₀ ⟨x,hx⟩
      refine ⟨Option ι,inferInstance,GM10.attachLeaf T t₀,
        fun t ↦ t.elim (insert v.1 B) χ,
        attach_vertex_decomposition v.2 htd t₀ B hB (fun _ h ↦ h),?_⟩
      intro t
      cases t with
      | some t =>
        intro x hx y hy hxy
        exact (hclique t hx hy hxy).2.2
      | none =>
        intro x hx y hy hxy
        rcases hx with rfl|hx
        · rcases hy with rfl|hy
          · exact (hxy rfl).elim
          · exact hy
        · rcases hy with rfl|hy
          · exact hx.symm
          · exact hBclique hx hy hxy
  exact main _ G hfin rfl hG

end GraphMinor.GM05
