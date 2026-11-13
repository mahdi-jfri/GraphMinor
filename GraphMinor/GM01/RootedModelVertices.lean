module

public import GraphMinor.GM01.RootedGraphs
public import GraphMinor.GM01.PathCombs
public import Mathlib.Data.Set.Card

/-!
# Vertex bounds for rooted models

The positive-height proof used for Graph Minors I, (1.1), page 55, chooses
a largest comb length. This choice needs a finite bound. Each branch of
a rooted model is nonempty and branches are disjoint, so choosing one
vertex in each branch gives an injective vertex map. In particular, the
comb spine cannot be longer than the target graph's vertex set.
-/

public section

namespace GraphMinor.GM01

open Graph

universe u v u' v'

/-- Choose a vertex in every branch. Disjointness makes the resulting map
on source vertices injective. -/
noncomputable def RootedMinorModel.vertexEmbedding
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G) :
    V(H.graph) ↪ V(G.graph) := by
  classical
  let chooseVertex (x : V(H.graph)) := (M.branch_connected x).1.choose
  have memBranch (x : V(H.graph)) : chooseVertex x ∈ M.branch x :=
    (M.branch_connected x).1.choose_spec
  refine
    { toFun := fun x ↦ ⟨chooseVertex x, M.branch_subset x (memBranch x)⟩
      inj' := ?_ }
  intro x y heq
  by_contra hxy
  have heq' : chooseVertex x = chooseVertex y := congrArg Subtype.val heq
  exact Set.disjoint_left.mp (M.branch_disjoint hxy) (memBranch x) (heq'.symm ▸ memBranch y)

/-- The chosen representative belongs to the branch it represents. -/
theorem RootedMinorModel.vertexEmbedding_mem_branch
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G) (x : V(H.graph)) :
    (M.vertexEmbedding x).val ∈ M.branch x := by
  exact (M.branch_connected x).1.choose_spec

/-- A rooted model in a finite target cannot have more vertices than the
target. This follows from the constructed vertex embedding. -/
theorem RootedMinorModel.ncard_vertices_le
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G)
    (hfin : V(G.graph).Finite) : V(H.graph).ncard ≤ V(G.graph).ncard := by
  let : Finite V(G.graph) := hfin.to_subtype
  exact Nat.card_le_card_of_injective M.vertexEmbedding M.vertexEmbedding.injective

/-- The length of a represented comb spine is bounded by the number of
target vertices. This proves finiteness of the set of lengths considered
when choosing a maximum on page 55. -/
theorem RootedMinorModel.pathComb_length_le {γ δ : ℕ} (hδ : 0 < δ)
    {α : Type u} {β : Type v} (G : RootedGraph α β)
    (M : RootedMinorModel (rootedPathComb γ δ hδ) G) (hfin : V(G.graph).Finite) :
    δ ≤ V(G.graph).ncard := by
  let f : Fin δ ↪ (pathComb γ δ).verts :=
    { toFun := fun i ↦ ⟨Sum.inl i, pathComb_spine_mem γ δ i⟩
      inj' := fun i j h ↦ Sum.inl.inj (congrArg Subtype.val h) }
  let : Finite (pathComb γ δ).verts := (pathComb_vertices_finite γ δ).to_subtype
  have hspine : δ ≤ (pathComb γ δ).verts.ncard := by
    have h := Nat.card_le_card_of_injective f f.injective
    rw [Nat.card_fin] at h
    exact h
  exact hspine.trans (M.ncard_vertices_le hfin)

end GraphMinor.GM01
