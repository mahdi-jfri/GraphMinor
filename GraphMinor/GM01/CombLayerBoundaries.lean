module

public import GraphMinor.GM01.PathCombs

/-!
# The first boundary vertex of a layer interval

Graph Minors I, page 58, defines `w_1` to be the root in layers zero
and one. In a later layer it is the spine vertex in the last early
block adjacent to the next block. In the subdivided comb this is the
cut centre at zero-based spine position `2ν(i-1)-1`.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph

/-- The vertex `w_1` preceding GM01 (4.8), page 58. The numerical bound
places its spine position in the represented comb. -/
def firstLayerBoundary {α β : Type*} {γ L : ℕ} (G : RootedGraph α β)
    (c : (pathComb γ L).verts → α) (ν i : ℕ) (hν : 0 < ν)
    (hbound : 2 * (ν * (i - 1)) ≤ L) : α :=
  if hi : i ≤ 1 then G.root.val
  else c ⟨Sum.inl ⟨2 * (ν * (i - 1)) - 1, by
    have hpos : 0 < ν * (i - 1) := Nat.mul_pos hν (Nat.sub_pos_of_lt (Nat.lt_of_not_ge hi))
    omega⟩, pathComb_spine_mem γ L _⟩

end GraphMinor.GM01
