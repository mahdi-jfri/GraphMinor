module

public import GraphMinor.GM08.Section17RootLeaves
import GraphMinor.GM08.Section4

/-!
# Simulations between grafts with root leaves

The root bijection assigns every new host leaf to a new target leaf's
branch. Hence a branch of an old target vertex contains no new host
leaf, and an old target edge cannot use a new host leaf edge. These
facts allow the collar leaves to be removed after the application of
VII (9.3) in VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v u' v'

/-- Every host root leaf lies in the branch of a target root leaf,
by the root bijection of a graft simulation. -/
theorem exists_root_branch_containing_new_leaf
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {X : Graft α β} {Y : Graft γ δ}
    {ηv : γ ⊕ γ → Set (α ⊕ α)} {ηe : δ ⊕ γ → β ⊕ α}
    (h : IsGraftSimulation (rootLeafGraft Y) (rootLeafGraft X) ηv ηe)
    {x : α} (hx : x ∈ X.T) :
    ∃ y ∈ Y.T, Sum.inr x ∈ ηv (Sum.inr y) := by
  have hxroot : Sum.inr x ∈ (rootLeafGraft X).T := by simpa using hx
  obtain ⟨z, hz⟩ := (graftRootFun_bijective h).2 ⟨Sum.inr x, hxroot⟩
  have hm := graftRootFun_mem h z
  have heq : (graftRootFun h z).1 = Sum.inr x := congrArg Subtype.val hz
  rw [heq] at hm
  obtain ⟨y, hy, hzy⟩ := z.2
  rw [← hzy] at hm
  exact ⟨y, hy, hm⟩

/-- Old target vertices have no new host leaf in their branch. -/
theorem new_leaf_not_mem_old_vertex_branch
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {X : Graft α β} {Y : Graft γ δ}
    {ηv : γ ⊕ γ → Set (α ⊕ α)} {ηe : δ ⊕ γ → β ⊕ α}
    (h : IsGraftSimulation (rootLeafGraft Y) (rootLeafGraft X) ηv ηe)
    {u : γ} (hu : u ∈ V(Y.G)) {x : α} (hx : x ∈ X.T) :
    Sum.inr x ∉ ηv (Sum.inl u) := by
  obtain ⟨y, hy, hxy⟩ := exists_root_branch_containing_new_leaf h hx
  have huV : Sum.inl u ∈ V((rootLeafGraft Y).G) := by simpa only [rootLeafGraft, inl_mem_rootLeafGraph_vertexSet] using hu
  have hyV : Sum.inr y ∈ V((rootLeafGraft Y).G) := by simpa only [rootLeafGraft, inr_mem_rootLeafGraph_vertexSet] using hy
  exact fun hxbranch => disjoint_left.mp
    (h.1.vertex_disjoint (Sum.inl u) huV (Sum.inr y) hyV (by intro heq; cases heq)) hxbranch hxy

/-- An old target edge is represented by an old host edge. A new host
edge is incident with a root leaf, whose assigned target branch is a
new target leaf and so cannot be incident with the old target edge. -/
theorem old_edge_image_is_old
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {X : Graft α β} {Y : Graft γ δ}
    {ηv : γ ⊕ γ → Set (α ⊕ α)} {ηe : δ ⊕ γ → β ⊕ α}
    (h : IsGraftSimulation (rootLeafGraft Y) (rootLeafGraft X) ηv ηe)
    {e : δ} (he : e ∈ E(Y.G)) :
    ∃ f ∈ E(X.G), ηe (Sum.inl e) = Sum.inl f := by
  have heV : Sum.inl e ∈ E((rootLeafGraft Y).G) := by simpa only [rootLeafGraft, inl_mem_rootLeafGraph_edgeSet] using he
  have hm := h.1.edge_mem (Sum.inl e) heV
  cases hmap : ηe (Sum.inl e) with
  | inl f =>
    refine ⟨f, ?_, rfl⟩
    simpa only [hmap, rootLeafGraft, inl_mem_rootLeafGraph_edgeSet] using hm
  | inr x =>
    have hx : x ∈ X.T := by
      simpa only [hmap, rootLeafGraft, inr_mem_rootLeafGraph_edgeSet] using hm
    obtain ⟨y, hy, hxy⟩ := exists_root_branch_containing_new_leaf h hx
    have hyV : Sum.inr y ∈ V((rootLeafGraft Y).G) := by simpa only [rootLeafGraft, inr_mem_rootLeafGraph_vertexSet] using hy
    have hinc : (rootLeafGraft Y).G.Inc (Sum.inl e) (Sum.inr y) :=
      (h.1.inc_iff (Sum.inr y) hyV (Sum.inl e) heV).mpr
        ⟨Sum.inr x, hxy, by rw [hmap]; exact ⟨Sum.inl x, hx, rfl, rfl⟩⟩
    obtain ⟨z, hz⟩ := hinc
    exfalso
    cases z <;> exact hz

/-- The branch of every old target vertex contains an old host vertex. -/
theorem exists_old_vertex_in_old_vertex_branch
    {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {X : Graft α β} {Y : Graft γ δ}
    {ηv : γ ⊕ γ → Set (α ⊕ α)} {ηe : δ ⊕ γ → β ⊕ α}
    (h : IsGraftSimulation (rootLeafGraft Y) (rootLeafGraft X) ηv ηe)
    {u : γ} (hu : u ∈ V(Y.G)) :
    ∃ x : α, Sum.inl x ∈ ηv (Sum.inl u) := by
  have huV : Sum.inl u ∈ V((rootLeafGraft Y).G) := by simpa only [rootLeafGraft, inl_mem_rootLeafGraph_vertexSet] using hu
  obtain ⟨z, hz⟩ := h.1.vertex_nonempty (Sum.inl u) huV
  cases z with
  | inl x => exact ⟨x, hz⟩
  | inr x =>
    have hxV := h.1.vertex_subset (Sum.inl u) huV hz
    have hx : x ∈ X.T := by simpa only [rootLeafGraft, inr_mem_rootLeafGraph_vertexSet] using hxV
    exact False.elim (new_leaf_not_mem_old_vertex_branch h hu hx hz)

end GraphMinor.GM08
