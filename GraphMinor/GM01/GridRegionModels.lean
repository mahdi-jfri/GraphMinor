module

public import GraphMinor.GM01.GridDiagramCoordinates
public import GraphMinor.GM01.RootedGraphs

/-!
# Moving a rooted model into a grid square

The copies in Figure 3 of Graph Minors I, pages 51–52, are translated
smaller squares. An injective edge-preserving map of grid vertices
gives a rooted model between the induced regions, with singleton
branches and the corresponding map on unordered pairs of endpoints.
This retains the chosen root of each smaller diagram.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- An injective map of grid vertices gives a rooted model between
any regions it maps into one another. This places the recursive copies
in the proof of GM01 (3.2), pages 51–52. -/
noncomputable def rootedModelOfGridRegionEmbedding {m n : ℕ}
    (S : Set (Fin m × Fin m)) (T : Set (Fin n × Fin n))
    (f : (Fin m × Fin m) ↪ (Fin n × Fin n))
    (hf : ∀ {x y}, (gridGraph m).Adj x y → (gridGraph n).Adj (f x) (f y))
    (hST : ∀ x ∈ S, f x ∈ T) (root : S) :
    RootedMinorModel
      (⟨(gridGraph m).induce S, root⟩ : RootedGraph _ _)
      (⟨(gridGraph n).induce T, ⟨f root.val, hST root.val root.property⟩⟩ :
        RootedGraph _ _) := by
  let H := (gridGraph m).induce S
  let G := (gridGraph n).induce T
  have hlink : ∀ e x y, H.IsLink e x y → G.IsLink (Sym2.map f e) (f x) (f y) := by
    intro e x y he
    change (gridGraph m).IsLink e x y ∧ x ∈ S ∧ y ∈ S at he
    have ha := hf (show (gridGraph m).Adj x y from ⟨e, he.1⟩)
    have ha' := (Graph.ofSimpleGraph_adj_iff (f x) (f y)).mp ha
    change ((Sym2.map f e = s(f x, f y) ∧ _) ∧ _ ∧ _)
    have heq : Sym2.map f e = s(f x, f y) := congrArg (Sym2.map f) he.1.1
    refine ⟨⟨heq, ?_⟩, hST x he.2.1, hST y he.2.2⟩
    rw [heq]
    exact ha'
  let ef : E(H) → E(G) := fun e ↦ ⟨Sym2.map f e.val, by
    obtain ⟨x, y, he⟩ := H.edge_mem_iff_exists_isLink e.val |>.mp e.property
    exact (hlink e.val x y he).edge_mem⟩
  refine
    { branch := fun x ↦ {f x.val}
      branch_subset := fun x ↦ singleton_subset_iff.mpr (hST x.val x.property)
      branch_disjoint := ?_
      branch_connected := ?_
      edgeMap := ⟨ef, ?_⟩
      edge_links := ?_
      root_mem := rfl }
  · intro x y hxy
    exact disjoint_singleton.mpr (fun h ↦ hxy (Subtype.ext (f.injective h)))
  · intro x
    refine ⟨⟨f x.val, rfl⟩, ?_⟩
    intro a ha b hb
    have ha' : a = f x.val := ha
    have hb' : b = f x.val := hb
    subst a
    subst b
    exact .refl
  · intro e e' h
    apply Subtype.ext
    exact Sym2.map.injective f.injective (congrArg Subtype.val h)
  · intro e x y he
    exact ⟨f x.val, rfl, f y.val, rfl, hlink e.val x.val y.val he⟩

end GraphMinor.GM01
