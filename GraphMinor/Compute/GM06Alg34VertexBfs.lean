module

public import GraphMinor.Compute.GM06Alg34VertexAdjList
public import GraphMinor.Compute.GM06Alg34VertexComponents
public import GraphMinor.Compute.Parse

/-!
# Computing one vertex component by breadth-first search

Use the constructed CSR lists to mark every vertex reachable from a
supplied source label. The size and source are read from
registers. The search preserves the drawing and CSR
arrays, so searches can be repeated to identify canonical component roots.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search the vertex graph from source register 187, writing
reachability bits in array 33 and using queue 34. -/
def gm06VertexBfsProg : Cmd :=
  bfsRegProg 4 187 30 31 32 33 34 190 191 192 193 194 195 196

/-- Reachability bits for one source vertex, computed from the supplied
finite endpoint graph. -/
def gm06VertexReachData (x : GM06DrawingData)
    (a : Fin x.n) : List ℕ :=
  List.ofFn (fun b : Fin x.n => if x.vertexGraph.Reachable a b then 1 else 0)

/-- One vertex search computes the exact component marks within a
quadratic bound and changes only its visited array, queue, and seven
scratch registers. -/
theorem gm06VertexBfsProg_exec {w : ℕ} (x : GM06DrawingData)
    (a : Fin x.n) (hw : 1 < 2 ^ w)
    (hN : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n) (hsource : s.regs 187 = a.val)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec w gm06VertexBfsProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 26 ∧
      s'.arrs 33 = gm06VertexReachData x a ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q < 190 ∨ 197 ≤ q → s'.regs q = s.regs q) := by
  have hspec := Triple.bfsRegProg_spec x.vertexGraph
    (adjListOf x.vertexGraph) a 4 187 30 31 32 33 34 190 191 192 193 194 195 196
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hw hN
  obtain ⟨s', t, hex, ht, hbuf⟩ := hspec s ⟨hsize, hsource, hlists, by simpa only [hlen] using hsquare⟩
  have htotal : totalAdjEntries (adjListOf x.vertexGraph) ≤ x.n * x.n := by
    unfold totalAdjEntries
    calc
      _ ≤ ∑ _ : Fin x.n, x.n :=
        Finset.sum_le_sum (fun u _ => (hlists.2 u).2.2.1)
      _ = _ := by simp
  change t ≤ 23 * x.n + 26 * totalAdjEntries (adjListOf x.vertexGraph) + 26 at ht
  refine ⟨s', t, hex, by omega, ?_, ?_, ?_⟩
  · rw [hbuf]
    unfold gm06VertexReachData
    congr 1
    funext b
    by_cases hb : x.vertexGraph.Reachable a b <;> simp [hb]
  · intro k hk₁ hk₂
    apply hex.arrs_eq_of_not_mem_writtenArrs
    simp [bfsRegProg, bfsLoopProg, bfsStepProg, queueInit, queuePop, queuePush,
      forList, forUp, Cmd.writtenArrs, hk₁, hk₂]
  · intro q hq
    apply hex.regs_eq_of_not_mem_writtenRegs
    have hwr : (bfsRegProg 4 187 30 31 32 33 34 190 191 192 193 194 195 196).writtenRegs =
        {190, 191, 192, 193, 194, 195, 196} := by decide
    rw [hwr]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hmem
    rcases hmem with hh | hh | hh | hh | hh | hh | hh <;> subst q <;> omega

end GraphMinor.Compute
