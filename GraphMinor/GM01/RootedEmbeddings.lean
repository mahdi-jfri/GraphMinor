module

public import GraphMinor.GM01.RootedGraphs
public import GraphMinor.GM01.Defs
public import GraphMinor.GM01.SubgraphIso

/-!
# Rooted models from embeddings

The rooted configurations in the proof of Graph Minors I, (1.1), can occur
as subgraphs as well as minor models. An injective graph map gives a model
with singleton branches. Changing the source by a root-preserving graph
isomorphism transfers a rooted minor model without changing its target.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph SimpleGraph

universe u v u' v' u'' v''

/-- Transfer a rooted model along a root-preserving isomorphism of its
source. The branches and edge images are those of the original model. -/
def RootedMinorModel.comapSource
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'} {ε : Type u''} {ζ : Type v''}
    {H : RootedGraph α β} {H' : RootedGraph γ δ} {G : RootedGraph ε ζ}
    (M : RootedMinorModel H G) (e : GraphMinor.Iso H'.graph H.graph)
    (hroot : e.vertexEquiv H'.root = H.root) : RootedMinorModel H' G where
  branch x := M.branch (e.vertexEquiv x)
  branch_subset x := M.branch_subset _
  branch_disjoint := fun _ _ hxy ↦ M.branch_disjoint (e.vertexEquiv.injective.ne hxy)
  branch_connected x := M.branch_connected _
  edgeMap := e.edgeEquiv.toEmbedding.trans M.edgeMap
  edge_links edge x y h := M.edge_links _ _ _ ((e.isLink_iff edge x y).mp h)
  root_mem := by rw [hroot]; exact M.root_mem

/-- An injective graph map gives a rooted minor model with singleton
branches. The source root is sent to the target root. -/
def rootedModelOfSimpleEmbedding {α : Type u} {β : Type v}
    (S : SimpleGraph α) (G : (⊤ : SimpleGraph β).Subgraph)
    (f : α ↪ β) (hverts : ∀ x, f x ∈ G.verts)
    (hadj : ∀ {x y}, S.Adj x y → G.Adj (f x) (f y)) (root : α) :
    RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, Set.mem_univ _⟩⟩ : RootedGraph α (Sym2 α))
      (⟨toGraph G, ⟨f root, hverts root⟩⟩ : RootedGraph β (Sym2 β)) := by
  let mapEdge : E(Graph.ofSimpleGraph S) → E(toGraph G) := fun e ↦
    ⟨Sym2.map f e.val, by
      obtain ⟨edge, he⟩ := e
      induction edge using Sym2.inductionOn with
      | hf x y =>
        have hs : S.Adj x y := he
        exact hadj hs⟩
  have hinj : Function.Injective mapEdge := by
    intro e e' heq
    apply Subtype.ext
    exact Sym2.map.injective f.injective (congrArg Subtype.val heq)
  refine
    { branch := fun x ↦ {f x.val}
      branch_subset := fun x ↦ Set.singleton_subset_iff.mpr (hverts x.val)
      branch_disjoint := ?_
      branch_connected := ?_
      edgeMap := ⟨mapEdge, hinj⟩
      edge_links := ?_
      root_mem := rfl }
  · intro x y hxy
    exact Set.disjoint_singleton.mpr (fun heq ↦ hxy (Subtype.ext (f.injective heq)))
  · intro x
    refine ⟨⟨f x.val, rfl⟩, ?_⟩
    intro a ha b hb
    change a ∈ {f x.val} at ha
    change b ∈ {f x.val} at hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact .refl
  · intro e x y he
    have hs : S.Adj x.val y.val := by
      have he' := e.property
      rw [he.1] at he'
      exact he'
    refine ⟨f x.val, rfl, f y.val, rfl, ?_⟩
    change Sym2.map f e.val = s(f x.val, f y.val) ∧ G.Adj (f x.val) (f y.val)
    exact ⟨congrArg (Sym2.map f) he.1, hadj hs⟩

/-- An injective map on the vertex set of a simple subgraph constructs a
rooted model. There is no need to define an injective map on unused ambient
vertices, which may form an infinite type. -/
noncomputable def rootedModelOfSubgraphEmbedding {α : Type u} {β : Type v}
    (H : (⊤ : SimpleGraph α).Subgraph) (G : (⊤ : SimpleGraph β).Subgraph)
    (f : H.verts ↪ β) (hverts : ∀ x, f x ∈ G.verts)
    (hadj : ∀ {x y : H.verts}, H.Adj x.val y.val → G.Adj (f x) (f y))
    (root : H.verts) :
    RootedMinorModel
      (⟨toGraph H, root⟩ : RootedGraph α (Sym2 α))
      (⟨toGraph G, ⟨f root, hverts root⟩⟩ : RootedGraph β (Sym2 β)) := by
  let M := rootedModelOfSimpleEmbedding H.coe G f hverts hadj root
  let e := subgraphSimpleGraphIso H
  let e' : GraphMinor.Iso (toGraph H) (Graph.ofSimpleGraph H.coe) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm x)
            (e.vertexEquiv.symm y)).symm }
  exact M.comapSource e' rfl

end GraphMinor.GM01
