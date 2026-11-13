module

public import GraphMinor.Kruskal.RootedGraph
public import Mathlib.Combinatorics.Graph.Simple
public import GraphMinor.Thomas.RootedTree

/-!
# The simple graph of a parent tree

Forgetting directions in a rooted tree gives a simple graph: a loop would
be a fixed non-root parent, and two different edge names with the same ends
would be a two-step parent cycle. The underlying simple graph is the one
already used in the library's translation of rooted trees.
-/

public section

namespace GraphMinor.Kruskal

open Graph Set GraphMinor.GM04

/-- Forgetting the edge directions of a rooted tree creates neither loops
nor parallel edges. -/
theorem rootedGraph_simple {ι : Type*} (T : RootedTree ι) : (rootedGraph T).Simple := by
  have hcycle {e f : ι} (he : e ∈ T.edges)
      (h₁ : T.parent e = f) (h₂ : T.parent f = e) : False := by
    have hi : T.parent^[2] e = e := by
      change T.parent (T.parent e) = e
      rw [h₁, h₂]
    exact T.ne_root_of_mem_edges he
      (T.eq_root_of_iterate_eq_self (T.mem_verts_of_mem_edges he) (by decide) hi)
  refine { toLoopless := ⟨?_⟩, eq_of_isLink := ?_ }
  · rintro e x ⟨he, h⟩
    rcases h with ⟨hx, hxe⟩ | ⟨hxe, hx⟩
    · exact T.parent_ne_self he (hx.symm.trans hxe)
    · exact T.parent_ne_self he (hx.symm.trans hxe)
  · rintro e f x y ⟨he, h₁⟩ ⟨hf, h₂⟩
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases h₂ with ⟨_, hef⟩ | ⟨hpf, hepf⟩
      · exact hef
      · exact (hcycle he hpf hepf.symm).elim
    · rcases h₂ with ⟨hepf, hpf⟩ | ⟨hef, _⟩
      · exact (hcycle he hpf hepf.symm).elim
      · exact hef

/-- The two definitions of the underlying simple graph have the same
vertices and adjacencies. The isomorphism is the identity on actual vertices. -/
def rootedGraphToSimpleIso {ι : Type*} (T : RootedTree ι) :
    (rootedGraph T).toSimpleGraph ≃g Thomas.toSimpleGraph T := by
  let := rootedGraph_simple T
  refine { toEquiv := Equiv.refl _, map_rel_iff' := ?_ }
  intro u v
  rw [(rootedGraph T).toSimpleGraph_adj_iff]
  change ((u.val ≠ T.root ∧ T.parent u.val = v.val) ∨
    (v.val ≠ T.root ∧ T.parent v.val = u.val)) ↔
      ∃ e, e ∈ T.edges ∧
        ((u.val = T.parent e ∧ v.val = e) ∨ (u.val = e ∧ v.val = T.parent e))
  constructor
  · rintro (⟨hne, hp⟩ | ⟨hne, hp⟩)
    · exact ⟨u.val, T.mem_edges.2 ⟨hne, u.property⟩, Or.inr ⟨rfl, hp.symm⟩⟩
    · exact ⟨v.val, T.mem_edges.2 ⟨hne, v.property⟩, Or.inl ⟨hp.symm, rfl⟩⟩
  · rintro ⟨e, he, h⟩
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv ▸ T.ne_root_of_mem_edges he, by rw [hv, hu]⟩
    · exact Or.inl ⟨hu ▸ T.ne_root_of_mem_edges he, by rw [hu, hv]⟩

end GraphMinor.Kruskal
