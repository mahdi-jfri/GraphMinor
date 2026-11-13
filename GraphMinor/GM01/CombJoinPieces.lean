module

public import GraphMinor.GM01.CombJoinModels

/-!
# Keeping a joined comb inside its two pieces and their path

The construction in Graph Minors I, (4.14), page 59, first joins the
middle segment to the late piece, and then joins the old prefix.
Perform the first join in the graph consisting of just its two
pieces and connecting path. Its vertex set is then known exactly,
which proves that the other joining path meets it only at the
required centre.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- The comb join on its actual union graph, used before the second
join in GM01 (4.14), page 59. -/
theorem exists_rooted_comb_join_piece {α β : Type*} {γ a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) {G : Graph α β} (G₁ G₂ : RootedGraph α β)
    (hG₁ : G₁.graph ≤ G) (hG₂ : G₂.graph ≤ G)
    (hdis : Disjoint V(G₁.graph) V(G₂.graph))
    (M₁ : RootedMinorModel (rootedPathComb γ a ha) G₁)
    (M₂ : RootedMinorModel (rootedPathComb γ b hb) G₂)
    {z : α} (hz : z ∈ M₁.branch (pathCombLastSpine γ a ha))
    {P : Graph α β} (hP : IsGraphPathWithEnds G P z G₂.root.val)
    (hP₁ : V(P) ∩ V(G₁.graph) = {z}) (hP₂ : V(P) ∩ V(G₂.graph) = {G₂.root.val}) :
    ∃ K : RootedGraph α β, K.graph ≤ G ∧
      V(K.graph) = V(G₁.graph) ∪ V(G₂.graph) ∪ V(P) ∧
      K.root.val = G₁.root.val ∧ HasRootedMinor (rootedPathComb γ (a + b) (by omega)) K := by
  let U := subgraphUnion G G₁.graph G₂.graph
  have hUG : U ≤ G := subgraphUnion_le hG₁ hG₂
  let K : RootedGraph α β := ⟨subgraphUnion G U P, ⟨G₁.root.val, Or.inl (Or.inl G₁.root.property)⟩⟩
  have hUK : U ≤ K.graph := le_subgraphUnion_left hUG hP.le
  have hPK : P ≤ K.graph := le_subgraphUnion_right hUG hP.le
  have h₁K : G₁.graph ≤ K.graph := (le_subgraphUnion_left hG₁ hG₂).trans hUK
  have h₂K : G₂.graph ≤ K.graph := (le_subgraphUnion_right hG₁ hG₂).trans hUK
  have hPathK : IsGraphPathWithEnds K.graph P z G₂.root.val := ⟨hPK, hP.2⟩
  exact ⟨K, subgraphUnion_le hUG hP.le, rfl, rfl,
    ⟨rootedModelOfCombJoin ha hb K G₁ G₂ h₁K h₂K rfl hdis M₁ M₂ hz hPathK hP₁ hP₂⟩⟩

end GraphMinor.GM01
