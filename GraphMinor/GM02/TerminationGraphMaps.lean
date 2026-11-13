module

public import GraphMinor.GM02.TerminationGraph
public import GraphMinor.GM02.TerminationVertices
public import GraphMinor.GM02.TerminationMaps

/-!
# Matching graphs under endpoint representation changes

A termination is encoded by the canonical edge list of its matching.
Restricting endpoints to their vertex subtype induces the matching on
that subtype. Renaming endpoints by a bijection pulls adjacency back by
the inverse bijection. These identities connect the path-problem
representation changes in II (3.2) to the endpoint-word rewrite program.
-/

public section
namespace GraphMinor.GM02
open Set SimpleGraph Classical
universe u u'

/-- Restricting endpoint types induces exactly the same matching. -/
theorem Termination.onVertices_pairGraph {α : Type u} {S : Set α} (A : Termination S) :
    A.onVertices.pairGraph = A.pairGraph.induce S := by
  ext a b
  rw [A.onVertices.pairGraph_adj_iff, SimpleGraph.induce_adj, A.pairGraph_adj_iff,
    A.mem_onVertices_pairs]
  rfl

/-- Changing the stated containing set leaves the matching unchanged. -/
theorem Termination.rebase_pairGraph {α : Type u} {S T : Set α} (A : Termination S)
    (h : A.support ⊆ T) : (A.rebase h).pairGraph = A.pairGraph := rfl

/-- A bijective endpoint renaming gives the matching with inverse-pulled
adjacency. -/
theorem Termination.mapEquiv_pairGraph {α : Type u} {α' : Type u'} {S : Set α}
    (A : Termination S) (e : α ≃ α') :
    (A.mapEmbedding e.toEmbedding).pairGraph = A.pairGraph.comap e.symm := by
  ext a b
  rw [(A.mapEmbedding e.toEmbedding).pairGraph_adj_iff, SimpleGraph.comap_adj,
    A.pairGraph_adj_iff]
  change s(a, b) ∈ A.pairs.image (Sym2.map e) ↔ s(e.symm a, e.symm b) ∈ A.pairs
  constructor
  · intro hp
    obtain ⟨p, hp, he⟩ := Finset.mem_image.1 hp
    have heq : p = s(e.symm a, e.symm b) := by
      apply Sym2.map.injective e.injective
      exact he.trans (by simp only [Sym2.map_mk, e.apply_symm_apply])
    exact heq ▸ hp
  · intro hp
    apply Finset.mem_image.2
    exact ⟨s(e.symm a, e.symm b), hp, by simp only [Sym2.map_mk, e.apply_symm_apply]⟩

/-- An injective endpoint renaming maps the entire matching graph. -/
theorem Termination.mapEmbedding_pairGraph {α : Type u} {α' : Type u'} {S : Set α}
    (A : Termination S) (f : α ↪ α') :
    (A.mapEmbedding f).pairGraph = A.pairGraph.map f := by
  ext a b
  rw [(A.mapEmbedding f).pairGraph_adj_iff, SimpleGraph.map_adj]
  constructor
  · intro hp
    obtain ⟨p, hp, he⟩ := Finset.mem_image.1 hp
    let u := p.out.1
    let v := p.out.2
    have hrep : s(u, v) = p := p.out_eq
    have hpair : s(u, v) ∈ A.pairs := by rw [hrep]; exact hp
    have huv : A.pairGraph.Adj u v := A.pairGraph_adj_iff.2 hpair
    have heq : s(f u, f v) = s(a, b) := (congrArg (Sym2.map f) hrep).trans he
    rcases Sym2.eq_iff.1 heq with ⟨hua, hvb⟩ | ⟨hub, hva⟩
    · exact ⟨u, v, huv, hua, hvb⟩
    · exact ⟨v, u, huv.symm, hva, hub⟩
  · rintro ⟨u, v, huv, hua, hvb⟩
    apply Finset.mem_image.2
    exact ⟨s(u, v), A.pairGraph_adj_iff.1 huv, by simp only [Sym2.map_mk, hua, hvb]⟩

end GraphMinor.GM02
