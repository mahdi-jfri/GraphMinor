module

public import GraphMinor.Compute.GM06Alg34VertexBfs
public import GraphMinor.Compute.GM06Alg34InteriorComponent
public import GraphMinor.Compute.GM06Alg34VertexMask
public import GraphMinor.Compute.Algorithm94Aux

/-!
# The retained-vertex mask for component deletion

Complement the computed component's visited bitset. The resulting
array is exactly the finite retained-vertex mask expected by the
induced payload builder. This pass uses the supplied vertex count and
computed bits, and has a linear bound with no geometric input data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Complement the component marks into retained-mask array 4. -/
def gm06InteriorMaskProg : Cmd := complBitSetProg 33 4 4 264

/-- The bitset complement is exactly the mask of labels outside the
searched component, in at most `14 * vertices + 6` steps. -/
theorem gm06InteriorMaskProg_exec {w : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06VertexReachData x a) (hsize : s.regs 4 = x.n) :
    ∃ s' t, Exec w gm06InteriorMaskProg s s' t ∧ t ≤ 14 * x.n + 6 ∧
      s'.arrs 4 = gm06VertexMask (x.interiorComponentSurvivors a) ∧
      (∀ A : ℕ, A ≠ 4 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 264 → s'.regs q = s.regs q) := by
  let C : Finset (Fin x.n) := Finset.univ.filter (fun b => x.vertexGraph.Reachable a b)
  have hbits : s.arrs 33 = bitSetList C := by
    rw [hmarks]
    simp only [gm06VertexReachData, bitSetList, C, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨s', t, hex, ht, hmask, harr, hreg⟩ :=
    complBitSetProg_exec C 33 4 4 264 (by decide) (by decide) hw hn
      (IsBitSet.of_bitSetList C 33 s hbits) hsize
  refine ⟨s', t, hex, by omega, ?_, harr, hreg⟩
  rw [hmask.arr_eq_bitSetList]
  unfold bitSetList gm06VertexMask
  congr 1
  funext b
  simp only [Finset.mem_sdiff, Finset.mem_univ, C, Finset.mem_filter, true_and,
    x.mem_interiorComponentSurvivors_iff]

end GraphMinor.Compute
