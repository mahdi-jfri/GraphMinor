module

public import GraphMinor.Compute.Join13Pack72

/-!
# Word bounds for the (4.1) core input

The core encoding has linear length. Each word is either a size, an endpoint,
a bit, or a parent or leaf index. The core's own side conditions bound all of
these by twice its size plus one.
-/

public section
namespace GraphMinor.Compute

/-- The packed core encoding has at most five words per unit of input size. -/
theorem length_encAlg41CoreIn_le {ξ B : ℕ} (x : Alg41CoreInput ξ B) :
    (encAlg41CoreIn x).length ≤ 5 * alg41CoreSize x := by
  have ht := x.ht_le
  simp only [encAlg41CoreIn, List.length_append, List.length_cons, List.length_nil,
    List.length_ofFn, length_bitSetList]
  dsimp [alg41CoreSize]
  omega

/-- Every core input word is bounded by twice the core input size plus one. -/
theorem mem_encAlg41CoreIn_le {ξ B : ℕ} (x : Alg41CoreInput ξ B)
    {a : ℕ} (ha : a ∈ encAlg41CoreIn x) : a ≤ 2 * alg41CoreSize x + 1 := by
  have ht := x.ht_le
  have hn : x.G.numVerts ≤ alg41CoreSize x := by dsimp [alg41CoreSize]; omega
  have hm : x.G.numEdges ≤ alg41CoreSize x := by dsimp [alg41CoreSize]; omega
  have htw : x.t ≤ 2 * alg41CoreSize x + 1 := by omega
  simp only [encAlg41CoreIn, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (((((ha | ha) | ha) | ha) | ha) | ha)
  · rcases ha with rfl | rfl | rfl <;> omega
  · obtain ⟨e, rfl⟩ := List.mem_ofFn.1 ha
    exact Nat.le_trans (Nat.le_of_lt (x.G.head e).2) (by omega)
  · obtain ⟨e, rfl⟩ := List.mem_ofFn.1 ha
    exact Nat.le_trans (Nat.le_of_lt (x.G.tail e).2) (by omega)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := getElem_bitSetList_le_one x.Z i hi
    omega
  · obtain ⟨z, rfl⟩ := List.mem_ofFn.1 ha
    have hp : x.p z.1 < x.t := by
      by_cases hz : z.1 = 0
      · rw [hz, x.hp0]; exact x.ht
      · exact (x.hp z.1 (by omega) z.2).trans z.2
    omega
  · obtain ⟨e, rfl⟩ := List.mem_ofFn.1 ha
    have := (x.τ e).2
    omega

end GraphMinor.Compute
