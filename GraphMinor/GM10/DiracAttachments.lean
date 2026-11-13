module

public import GraphMinor.GM10.DiracAbsorption

/-!
# Three attachments to a cycle

In the low-valency argument used for Graph Minors X, (4.2), absorbing
a neighbour of the maximal connected set leaves a forest. Two vertices
of this forest have at most one remaining neighbour, so each has a
neighbour in the connected set. Maximality places both on the original
cycle. Together with the absorbed vertex, they give three attachments.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Classical

universe u

private theorem neighbor_in_deleted_set_of_small_neighbor_set
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ x, 3 ≤ (G.neighborSet x).ncard) (H : Set V) (z : V)
    (x : ((insert z H)ᶜ : Set V))
    (hx : ((G.induce (insert z H)ᶜ).neighborSet x).ncard ≤ 1) :
    ∃ a ∈ H, G.Adj a x.val := by
  classical
  by_contra! hno
  let F : Set V := (insert z H)ᶜ
  have hsub : G.neighborSet x.val ⊆
      (Subtype.val '' (G.induce F).neighborSet x) ∪ {z} := by
    intro y hxy
    by_cases hyz : y = z
    · exact Or.inr hyz
    · have hyH : y ∉ H := fun hy ↦ hno y hy hxy.symm
      have hyF : y ∈ F := by
        rintro (h | h)
        · exact hyz h
        · exact hyH h
      exact Or.inl ⟨⟨y, hyF⟩, hxy, rfl⟩
  have hbound := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (Set.ncard_union_le _ _)
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_singleton] at hbound
  dsimp only [F] at hbound
  have := hdeg x.val
  omega

/-- The maximal-set argument gives a cycle disjoint from a connected set
and three distinct vertices of the cycle adjacent to that set. This is
the configuration needed for the external low-valency input to X (4.2). -/
theorem exists_cycle_with_three_attachments
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hconn : G.Connected)
    (hdeg : ∀ x, 3 ≤ (G.neighborSet x).ncard) :
    ∃ (H : Set V) (z : V) (p : G.Walk z z),
      (G.induce H).Connected ∧ p.IsCycle ∧
      (∀ x ∈ p.support, x ∉ H) ∧ (∃ a ∈ H, G.Adj a z) ∧
      ∃ x y, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∈ p.support ∧ y ∈ p.support ∧
        (∃ a ∈ H, G.Adj a x) ∧ (∃ a ∈ H, G.Adj a y) := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨H, hH, ⟨b, c, hc, havoid⟩, hmax⟩ :=
    exists_maximal_connected_set_with_cycle_complement G hdeg
  obtain ⟨a⟩ := hH.nonempty
  obtain ⟨r⟩ := hconn a.val b
  obtain ⟨d, _, hdH, hdz⟩ := r.exists_boundary_dart H a.property
    (havoid b c.start_mem_support)
  let z := d.snd
  have hzC : z ∈ c.support := boundary_neighbor_mem_cycle_of_maximal_connected_set
    G H hH hmax c hc havoid hdH hdz d.adj
  let p := c.rotate z hzC
  have hp : p.IsCycle := hc.rotate hzC
  have hpavoid : ∀ x ∈ p.support, x ∉ H := by
    intro x hx
    exact havoid x ((SimpleGraph.Walk.mem_support_rotate_iff c z hzC).1 hx)
  have hforest : (G.induce (insert z H)ᶜ).IsAcyclic :=
    acyclic_complement_insert_of_maximal_connected_set G H hH hmax hdH hdz d.adj
  let F : Set V := (insert z H)ᶜ
  have hmemF : ∀ x ∈ p.support, x ≠ z → x ∈ F := by
    intro x hx hxz
    rintro (h | h)
    · exact hxz h
    · exact hpavoid x hx h
  have hsnd : p.snd ∈ F := hmemF p.snd (p.getVert_mem_support 1)
    (p.adj_snd hp.not_nil).ne.symm
  have hpen : p.penultimate ∈ F := hmemF p.penultimate
    (List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hp.not_nil))
    (p.adj_penultimate hp.not_nil).ne
  let : Nontrivial F := ⟨⟨⟨p.snd, hsnd⟩, ⟨p.penultimate, hpen⟩,
    fun h ↦ hp.snd_ne_penultimate (congrArg (fun x : F ↦ x.val) h)⟩⟩
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_two_small_neighbor_sets_of_acyclic (G.induce F) hforest
  obtain ⟨ax, hax, haxx⟩ := neighbor_in_deleted_set_of_small_neighbor_set G hdeg H z x hx
  obtain ⟨ay, hay, hayy⟩ := neighbor_in_deleted_set_of_small_neighbor_set G hdeg H z y hy
  have hxH : x.val ∉ H := fun h ↦ x.property (Or.inr h)
  have hyH : y.val ∉ H := fun h ↦ y.property (Or.inr h)
  have hxC : x.val ∈ p.support := (SimpleGraph.Walk.mem_support_rotate_iff c z hzC).2
    (boundary_neighbor_mem_cycle_of_maximal_connected_set G H hH hmax c hc havoid hax hxH haxx)
  have hyC : y.val ∈ p.support := (SimpleGraph.Walk.mem_support_rotate_iff c z hzC).2
    (boundary_neighbor_mem_cycle_of_maximal_connected_set G H hH hmax c hc havoid hay hyH hayy)
  refine ⟨H, z, p, hH, hp, hpavoid, ⟨d.fst, hdH, d.adj⟩, x.val, y.val, ?_, ?_, ?_,
    hxC, hyC, ⟨ax, hax, haxx⟩, ⟨ay, hay, hayy⟩⟩
  · exact fun h ↦ hxy (Subtype.ext h)
  · exact fun h ↦ x.property (Or.inl h)
  · exact fun h ↦ y.property (Or.inl h)

end GraphMinor.GM10
