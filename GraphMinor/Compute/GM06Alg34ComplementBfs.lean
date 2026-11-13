module

public import GraphMinor.Compute.GM06Alg34ComplementAdjList
public import GraphMinor.Compute.GM06Alg34RegionRoots
public import GraphMinor.Compute.Parse

/-!
# Computing one complement component by breadth-first search

Use the constructed CSR lists to mark every cell reachable from a
supplied packed source label. The size and source are read from
registers. The search preserves the drawing, closure table, and CSR
arrays, so searches can be repeated to identify canonical region roots.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search the complement graph from source register 187, writing
reachability bits in array 33 and using queue 34. -/
def gm06ComplementBfsProg : Cmd :=
  bfsRegProg 4 187 30 31 32 33 34 190 191 192 193 194 195 196

/-- Reachability bits for one source cell, computed from the supplied
finite complement graph. -/
def gm06ComplementReachData (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) : List ℕ :=
  List.ofFn (fun b : Fin x.cellCount => if (x.complementGraph vs).Reachable a b then 1 else 0)

/-- One complement search computes the exact component marks within a
quadratic bound and changes only its visited array, queue, and seven
scratch registers. -/
theorem gm06ComplementBfsProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.cellCount) (hsource : s.regs 187 = a.val)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06ComplementBfsProg s s' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 23 * x.cellCount + 26 ∧
      s'.arrs 33 = gm06ComplementReachData x vs a ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q < 190 ∨ 197 ≤ q → s'.regs q = s.regs q) := by
  have hspec := Triple.bfsRegProg_spec (x.complementGraph vs)
    (adjListOf (x.complementGraph vs)) a 4 187 30 31 32 33 34 190 191 192 193 194 195 196
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hw hN
  obtain ⟨s', t, hex, ht, hbuf⟩ := hspec s ⟨hsize, hsource, hlists, by simpa only [hlen] using hsquare⟩
  have htotal : totalAdjEntries (adjListOf (x.complementGraph vs)) ≤ x.cellCount * x.cellCount := by
    unfold totalAdjEntries
    calc
      _ ≤ ∑ _ : Fin x.cellCount, x.cellCount :=
        Finset.sum_le_sum (fun u _ => (hlists.2 u).2.2.1)
      _ = _ := by simp
  change t ≤ 23 * x.cellCount + 26 * totalAdjEntries (adjListOf (x.complementGraph vs)) + 26 at ht
  refine ⟨s', t, hex, by omega, ?_, ?_, ?_⟩
  · rw [hbuf]
    unfold gm06ComplementReachData
    congr 1
    funext b
    by_cases hb : (x.complementGraph vs).Reachable a b <;> simp [hb]
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
