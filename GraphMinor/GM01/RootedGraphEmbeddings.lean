module

public import GraphMinor.GM01.RootedBranchModels

/-!
# Rooted simple embeddings into general graphs

The comb concatenation in Graph Minors I, (4.10), page 58, first builds
a model of two joined source combs. An injective source map preserving
adjacency transfers the longer comb to that source. Singleton branches
supply the transfer model, and connectedness of those branches is
witnessed by their single vertex.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- An injective map preserving adjacency into a rooted general graph
gives a singleton-branch model when it sends the source root to the
target root. -/
noncomputable def rootedModelOfGraphEmbedding {α β ν : Type*} (S : SimpleGraph ν)
    (G : RootedGraph α β) (f : ν ↪ α) (hverts : ∀ v, f v ∈ V(G.graph))
    (hAdj : ∀ {a b}, S.Adj a b → G.graph.Adj (f a) (f b))
    (root : ν) (hroot : G.root.val = f root) :
    RootedMinorModel (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν)) G := by
  apply rootedModelOfBranchSets S G (fun v ↦ {f v})
    (fun v ↦ Set.singleton_subset_iff.mpr (hverts v))
    (fun u v huv ↦ Set.disjoint_singleton.mpr (fun h ↦ huv (f.injective h)))
    (fun v ↦ ⟨⟨f v, rfl⟩, fun a ha b hb ↦ by
      have ha' : a = f v := ha
      have hb' : b = f v := hb
      subst a
      subst b
      exact .refl⟩)
    (root := root) (hroot := hroot)
  intro a b hab
  obtain ⟨e, he⟩ := hAdj hab
  exact ⟨e, f a, rfl, f b, rfl, he⟩

end GraphMinor.GM01
