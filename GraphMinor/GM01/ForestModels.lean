module

public import GraphMinor.GM01.ForestTrees
import GraphMinor.GM01.Basic

/-!
# Branch sets in the forest-exclusion trees

The proof of Graph Minors I, (1.1), page 51, uses the fact that every finite
forest is a minor of some `Y_ℓ`. To build its branch sets by removing leaves,
keep an outer vertex in each branch set. Adding a child to that vertex
extends the branch set and keeps it connected. Children of distinct outer
vertices lie outside the old tree and have distinct parents.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- A child is different from its parent since its depth is larger. -/
theorem forestTreeChild_ne_parent (bit : Bool) (v : ForestTreeVertex) :
    forestTreeChild bit v ≠ v := by
  intro heq
  have hd := forestTreeDepth_child bit v
  rw [heq] at hd
  exact Nat.add_one_ne_self _ hd.symm

/-- Extend a branch set by the edge to a chosen child of one of its outer
vertices. This construction contains no assumption about the source forest. -/
def forestTreeBranchGrow (K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph)
    (v : ForestTreeVertex) (bit : Bool) :
    (⊤ : SimpleGraph ForestTreeVertex).Subgraph :=
  K ⊔ (⊤ : SimpleGraph ForestTreeVertex).subgraphOfAdj
    ((top_adj _ _).2 (forestTreeChild_ne_parent bit v).symm)

/-- The old branch set is retained. -/
theorem le_forestTreeBranchGrow (K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph)
    (v : ForestTreeVertex) (bit : Bool) : K ≤ forestTreeBranchGrow K v bit :=
  le_sup_left

/-- Attaching the edge adds just its new endpoint when the parent is already
in the branch set. -/
theorem forestTreeBranchGrow_verts {K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph}
    {v : ForestTreeVertex} (hv : v ∈ K.verts) (bit : Bool) :
    (forestTreeBranchGrow K v bit).verts = insert (forestTreeChild bit v) K.verts := by
  rw [forestTreeBranchGrow, Subgraph.verts_sup, subgraphOfAdj_verts]
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (hx | hx | hx)
    · exact Or.inr hx
    · exact Or.inr (hx ▸ hv)
    · exact Or.inl hx
  · rintro (hx | hx)
    · exact Or.inr (Or.inr hx)
    · exact Or.inl hx

/-- An extended branch set lies in the next tree. -/
theorem forestTreeBranchGrow_le {ℓ : ℕ}
    {K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph}
    (hK : K ≤ forestTree ℓ) {v : ForestTreeVertex} (hv : v ∈ K.verts) (bit : Bool) :
    forestTreeBranchGrow K v bit ≤ forestTree (ℓ + 1) :=
  sup_le (hK.trans (forestTree_mono (Nat.le_succ ℓ)))
    (subgraphOfAdj_le_of_adj _ (forestTree_adj_child (hK.1 hv) bit))

/-- The edge to the chosen child meets the old branch set at its parent,
so the extended branch set is connected. -/
theorem forestTreeBranchGrow_connected
    {K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph} (hK : K.Connected)
    {v : ForestTreeVertex} (hv : v ∈ K.verts) (bit : Bool) :
    (forestTreeBranchGrow K v bit).Connected := by
  apply Subgraph.connected_sup hK.preconnected (Subgraph.subgraphOfAdj_connected _).preconnected
  exact ⟨v, hv, by simp⟩

/-- Two disjoint branch sets remain disjoint when each is extended at an
outer vertex, since their new vertices have different parents. -/
theorem forestTreeBranchGrow_disjoint {ℓ : ℕ}
    {K L : (⊤ : SimpleGraph ForestTreeVertex).Subgraph}
    (hK : K ≤ forestTree ℓ) (hL : L ≤ forestTree ℓ)
    (hdisj : Disjoint K.verts L.verts)
    {v w : ForestTreeVertex} (hv : v ∈ K.verts) (hw : w ∈ L.verts)
    (hvd : forestTreeDepth v = ℓ) (hwd : forestTreeDepth w = ℓ) (a b : Bool) :
    Disjoint (forestTreeBranchGrow K v a).verts (forestTreeBranchGrow L w b).verts := by
  rw [forestTreeBranchGrow_verts hv, forestTreeBranchGrow_verts hw]
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hparent := forestTreeChild_parent_injective (hx.symm.trans hy)
    exact Set.disjoint_left.mp hdisj hv (hparent.symm ▸ hw)
  · subst x
    exact forestTreeChild_not_mem hvd a (hL.1 hy)
  · subst x
    exact forestTreeChild_not_mem hwd b (hK.1 hx)
  · exact Set.disjoint_left.mp hdisj hx hy

/-- A vertex outside the current tree stays outside an old branch set. An
outer vertex therefore gives two distinct possible new singleton branch sets. -/
theorem forestTreeChild_not_mem_branch {ℓ : ℕ}
    {K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph} (hK : K ≤ forestTree ℓ)
    {v : ForestTreeVertex} (hvd : forestTreeDepth v = ℓ) (bit : Bool) :
    forestTreeChild bit v ∉ K.verts :=
  fun h ↦ forestTreeChild_not_mem hvd bit (hK.1 h)

/-- Equal chosen children have the same bit as well as the same parent. -/
theorem forestTreeChild_bit_injective {a b : Bool} {v w : ForestTreeVertex}
    (h : forestTreeChild a v = forestTreeChild b w) : a = b := by
  have hp := forestTreeChild_parent_injective h
  subst w
  cases a <;> cases b
  · rfl
  · exact False.elim (forestTreeChild_false_ne_true v h)
  · exact False.elim (forestTreeChild_false_ne_true v h.symm)
  · rfl

/-- A new child is outside an extended branch set unless it is the chosen
new vertex of that branch set. -/
theorem forestTreeChild_not_mem_grow {ℓ : ℕ}
    {K : (⊤ : SimpleGraph ForestTreeVertex).Subgraph} (hK : K ≤ forestTree ℓ)
    {v w : ForestTreeVertex} (hv : v ∈ K.verts)
    (hwd : forestTreeDepth w = ℓ) {a b : Bool}
    (hne : forestTreeChild b w ≠ forestTreeChild a v) :
    forestTreeChild b w ∉ (forestTreeBranchGrow K v a).verts := by
  rw [forestTreeBranchGrow_verts hv]
  intro h
  rcases h with h | h
  · exact hne h
  · exact forestTreeChild_not_mem_branch hK hwd b h

end GraphMinor.GM01
