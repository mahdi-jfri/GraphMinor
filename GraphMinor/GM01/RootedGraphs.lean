module

public import GraphMinor.Minor.Model

/-!
# Rooted graphs and rooted minor models

The proof of Graph Minors I, (1.1), uses the rooted trees in Section 3.
We state the definition of a rooted minor by its branch sets, its injection
on edges, and its root condition, exactly as in (M1)–(M4), pages 52–53.
The identity model shows that each rooted graph is a rooted minor of itself.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph

universe u v u' v'

/-- Graph Minors I, Section 3, page 52: a rooted graph is a graph with one
vertex distinguished as its root. -/
structure RootedGraph (α : Type u) (β : Type v) where
  graph : Graph α β
  root : V(graph)

/-- Graph Minors I, Section 3, (M1)–(M4), pages 52–53. The branch of each
source vertex is a subset of the target vertex set. Branches are disjoint,
induce connected graphs, and meet the corresponding ends of an injection on
edges. The target root belongs to the branch of the source root. -/
structure RootedMinorModel {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    (H : RootedGraph α β) (G : RootedGraph γ δ) where
  branch : V(H.graph) → Set γ
  branch_subset : ∀ x, branch x ⊆ V(G.graph)
  branch_disjoint : Pairwise fun x y ↦ Disjoint (branch x) (branch y)
  branch_connected : ∀ x, GraphConnected (G.graph.induce (branch x))
  edgeMap : E(H.graph) ↪ E(G.graph)
  edge_links : ∀ (e : E(H.graph)) (x y : V(H.graph)), H.graph.IsLink e x y →
    ∃ a ∈ branch x, ∃ b ∈ branch y, G.graph.IsLink (edgeMap e) a b
  root_mem : G.root.val ∈ branch H.root

/-- A rooted minor is the existence of the branch-set model in (M1)–(M4)
of Graph Minors I, Section 3, pages 52–53. -/
def HasRootedMinor {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    (H : RootedGraph α β) (G : RootedGraph γ δ) : Prop :=
  Nonempty (RootedMinorModel H G)

/-- The identity model uses singleton branches and the identity edge map. -/
def RootedMinorModel.refl {α : Type u} {β : Type v} (G : RootedGraph α β) :
    RootedMinorModel G G where
  branch x := {x.val}
  branch_subset x := Set.singleton_subset_iff.mpr x.property
  branch_disjoint := by
    intro x y hxy
    exact Set.disjoint_singleton.mpr (fun heq ↦ hxy (Subtype.ext heq))
  branch_connected x := by
    refine ⟨⟨x.val, rfl⟩, ?_⟩
    intro a ha b hb
    change a ∈ {x.val} at ha
    change b ∈ {x.val} at hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact .refl
  edgeMap := Function.Embedding.refl _
  edge_links e x y he := ⟨x.val, rfl, y.val, rfl, he⟩
  root_mem := rfl

/-- Every rooted graph has itself as a rooted minor. -/
theorem HasRootedMinor.refl {α : Type u} {β : Type v} (G : RootedGraph α β) :
    HasRootedMinor G G :=
  ⟨RootedMinorModel.refl G⟩

/-- Enlarging a target graph preserves a model when the distinguished root
is unchanged. -/
def RootedMinorModel.mono {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {H : RootedGraph α β} {G G' : RootedGraph γ δ}
    (M : RootedMinorModel H G) (h : G.graph ≤ G'.graph)
    (hroot : G.root.val = G'.root.val) : RootedMinorModel H G' where
  branch := M.branch
  branch_subset x := (M.branch_subset x).trans h.vertexSet_mono
  branch_disjoint := M.branch_disjoint
  branch_connected x := by
    refine ⟨(M.branch_connected x).1, ?_⟩
    intro a ha b hb
    have hr := (M.branch_connected x).2 a ha b hb
    apply Relation.ReflTransGen.mono ?_ a b hr
    intro c d hcd
    obtain ⟨e, he⟩ := hcd
    exact ⟨e, he.1.mono h, he.2⟩
  edgeMap := M.edgeMap.trans
    ⟨fun e ↦ ⟨e.val, h.edgeSet_mono e.property⟩, fun _ _ heq ↦
      Subtype.ext (congrArg (fun e : E(G'.graph) ↦ e.val) heq)⟩
  edge_links e x y he := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.edge_links e x y he
    exact ⟨a, ha, b, hb, hab.mono h⟩
  root_mem := hroot ▸ M.root_mem

end GraphMinor.GM01
