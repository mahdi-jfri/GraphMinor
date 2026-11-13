module

public import GraphMinor.Compute.GM02TopologicalInput

/-!
# Active edge arrays and actual graph deletion

The machine keeps the supplied edge positions and marks a removed edge
with zero. An edge is retained precisely when its array entry is one.
Updating one entry to zero deletes that actual edge from the represented
subgraph. Vertex names and isolated vertices remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Classical
universe u

/-- The subgraph retaining exactly the edge positions marked one in the array. -/
def gm02ActiveGraph {A : Type u} (G : Graph A ℕ) (flags : List ℕ) : Graph A ℕ :=
  G.restrict {e | flags[e]? = some 1}

/-- Active edge flags leave the entire supplied vertex set unchanged. -/
theorem gm02ActiveGraph_vertices {A : Type u} (G : Graph A ℕ) (flags : List ℕ) :
    V(gm02ActiveGraph G flags) = V(G) := rfl

/-- The active graph is a subgraph of the supplied graph. -/
theorem gm02ActiveGraph_le {A : Type u} (G : Graph A ℕ) (flags : List ℕ) :
    gm02ActiveGraph G flags ≤ G := Graph.restrict_le

/-- An active link is an original link whose actual edge position is marked one. -/
theorem gm02ActiveGraph_isLink_iff {A : Type u} (G : Graph A ℕ) (flags : List ℕ)
    (e : ℕ) (a b : A) :
    (gm02ActiveGraph G flags).IsLink e a b ↔ flags[e]? = some 1 ∧ G.IsLink e a b := Iff.rfl

/-- Initial all-one flags retain every supplied edge. -/
theorem gm02ActiveGraph_replicate {A : Type u} (G : Graph A ℕ) (m : ℕ)
    (hE : E(G) ⊆ Set.Iio m) : gm02ActiveGraph G (List.replicate m 1) = G := by
  apply (Graph.restrict_eq_self_iff _ _).2
  intro e he
  change (List.replicate m 1)[e]? = some 1
  rw [List.getElem?_replicate]
  exact ite_eq_left (show e < m from hE he)

/-- A zero update removes precisely its own edge from the active predicate. -/
theorem gm02ActiveFlag_set_zero (flags : List ℕ) (e f : ℕ) (he : e < flags.length) :
    (flags.set e 0)[f]? = some 1 ↔ flags[f]? = some 1 ∧ f ≠ e := by
  by_cases hef : e = f
  · subst f
    rw [List.getElem?_set_self he]
    simp
  · rw [List.getElem?_set_ne hef]
    constructor
    · intro h; exact ⟨h, Ne.symm hef⟩
    · exact And.left

/-- The machine's zero update represents deletion of that actual edge. -/
theorem gm02ActiveGraph_set_zero {A : Type u} (G : Graph A ℕ) (flags : List ℕ)
    (e : ℕ) (he : e < flags.length) :
    gm02ActiveGraph G (flags.set e 0) = (gm02ActiveGraph G flags).deleteEdges {e} := by
  refine Graph.ext rfl fun f a b => ?_
  rw [gm02ActiveGraph_isLink_iff, Graph.deleteEdges_isLink, gm02ActiveGraph_isLink_iff,
    gm02ActiveFlag_set_zero flags e f he]
  change ((flags[f]? = some 1 ∧ f ≠ e) ∧ G.IsLink f a b) ↔
    ((flags[f]? = some 1 ∧ G.IsLink f a b) ∧ f ≠ e)
  tauto

/-- Clearing a flag preserves the property that every flag is zero or one. -/
theorem gm02ActiveFlags_set_zero_bits (flags : List ℕ) (e : ℕ)
    (hbits : ∀ b ∈ flags, b ≤ 1) : ∀ b ∈ flags.set e 0, b ≤ 1 := by
  intro b hb
  rcases List.mem_or_eq_of_mem_set hb with hb | hb
  · exact hbits b hb
  · exact hb ▸ (by decide : 0 ≤ 1)

end GraphMinor.Compute
