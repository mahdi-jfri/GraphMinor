module

public import GraphMinor.GM01.RootedGraphs
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Rooted models from connected branch sets

The contraction step in Graph Minors I, (4.1), page 55, specifies disjoint
connected pieces joined by edges. For a simple source, choosing one such
edge per source edge gives an injective edge map: if two choices coincide,
their ends belong to the same two branches, which determines the source
edge. The root condition then gives a rooted model with these actual
branch sets.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Construct a rooted model from its branch sets and the edges joining
them. Edge injectivity follows from disjointness and simplicity of the
source, rather than being an extra assumption on the chosen edges. -/
noncomputable def rootedModelOfBranchSets {α γ δ : Type*} (S : SimpleGraph α)
    (G : RootedGraph γ δ) (B : α → Set γ) (hB : ∀ v, B v ⊆ V(G.graph))
    (hdisj : Pairwise fun u v ↦ Disjoint (B u) (B v))
    (hconn : ∀ v, GraphConnected (G.graph.induce (B v)))
    (hadj : ∀ {u v}, S.Adj u v → ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y)
    (root : α) (hroot : G.root.val ∈ B root) :
    RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph α (Sym2 α)) G := by
  classical
  have choose_edge : ∀ e : S.edgeSet, ∃ f : E(G.graph),
      ∀ a b, e.val = s(a,b) → ∃ x ∈ B a, ∃ y ∈ B b, G.graph.IsLink f x y := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf u v =>
      obtain ⟨f, x, hx, y, hy, hxy⟩ := hadj he
      refine ⟨⟨f, hxy.edge_mem⟩, ?_⟩
      intro a b hab
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨x, hx, y, hy, hxy⟩
      · exact ⟨y, hy, x, hx, hxy.symm⟩
  let f (e : S.edgeSet) : E(G.graph) := (choose_edge e).choose
  have spec (e : S.edgeSet) (a b : α) (he : e.val = s(a,b)) :
      ∃ x ∈ B a, ∃ y ∈ B b, G.graph.IsLink (f e) x y :=
    (choose_edge e).choose_spec a b he
  have same_branch : ∀ {u v : α} {x : γ}, x ∈ B u → x ∈ B v → u = v := by
    intro u v x hx hy
    by_contra huv
    exact disjoint_left.mp (hdisj huv) hx hy
  have hinj : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ heq
    apply Subtype.ext
    induction e using Sym2.inductionOn with
    | hf u v =>
      induction e' using Sym2.inductionOn with
      | hf a b =>
        obtain ⟨x, hx, y, hy, hxy⟩ := spec ⟨s(u,v), he⟩ u v rfl
        obtain ⟨x', hx', y', hy', hxy'⟩ := spec ⟨s(a,b), he'⟩ a b rfl
        change G.graph.IsLink (f ⟨s(u,v), he⟩) x y at hxy
        rw [heq] at hxy
        rcases hxy.eq_and_eq_or_eq_and_eq hxy' with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
        · have hua := same_branch hx (hxx ▸ hx')
          have hvb := same_branch hy (hyy ▸ hy')
          exact Sym2.eq_iff.mpr (Or.inl ⟨hua, hvb⟩)
        · have hub := same_branch hx (hxy ▸ hy')
          have hva := same_branch hy (hyx ▸ hx')
          exact Sym2.eq_iff.mpr (Or.inr ⟨hub, hva⟩)
  refine
    { branch := fun v ↦ B v.val
      branch_subset := fun v ↦ hB v.val
      branch_disjoint := ?_
      branch_connected := fun v ↦ hconn v.val
      edgeMap := ⟨f, hinj⟩
      edge_links := ?_
      root_mem := hroot }
  · intro u v huv
    exact hdisj (fun heq ↦ huv (Subtype.ext heq))
  · intro e u v he
    exact spec e u.val v.val he.1

/-- The branch constructor retains exactly the supplied branch sets. -/
theorem rootedModelOfBranchSets_branch {α γ δ : Type*} (S : SimpleGraph α)
    (G : RootedGraph γ δ) (B : α → Set γ) (hB : ∀ v, B v ⊆ V(G.graph))
    (hdisj : Pairwise fun u v ↦ Disjoint (B u) (B v))
    (hconn : ∀ v, GraphConnected (G.graph.induce (B v)))
    (hadj : ∀ {u v}, S.Adj u v → ∃ e x, x ∈ B u ∧ ∃ y, y ∈ B v ∧ G.graph.IsLink e x y)
    (root : α) (hroot : G.root.val ∈ B root) (v : V(Graph.ofSimpleGraph S)) :
    (rootedModelOfBranchSets S G B hB hdisj hconn hadj root hroot).branch v = B v.val := by
  unfold rootedModelOfBranchSets
  rfl

end GraphMinor.GM01
