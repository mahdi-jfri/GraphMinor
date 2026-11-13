module

public import GraphMinor.Compute.Algorithm99Order
public import GraphMinor.Compute.Algorithm99OrderEquiv
import Mathlib.Data.List.GetD

/-!
# Reordering leaf assignments into the caller's edge order

The stable tail sort writes the assignment of each active-pair edge at the
index of the same individual edge in the caller's enumeration. The result is
the leaf map composed with `computeToMultiEdgeEquiv`, exactly as required for
the branch-decomposition interface.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Specializing the stable sorter to an edge-tail stream produces the exact
leaf assignment in the caller's edge order. The vertex-count register supplies
`n + 1`, including the unused final bucket. -/
theorem alg99TailSortProg_exec_leaves {w n : ℕ} (G : MultiDigraph n)
    (τ : Fin G.numEdges → ℕ) (a r r_n : ℕ)
    (hw : 1 < 2 ^ w) (hn : n + 1 < 2 ^ w) (hm : G.numEdges < 2 ^ w)
    (hτ : ∀ i, τ i < 2 ^ w) (s : State)
    (hkeys : s.arrs a = List.ofFn (fun i : Fin G.numEdges => (G.edgeEndpoints i).1.1))
    (hvals : s.arrs (a + 1) = List.ofFn τ) (hrn : s.regs r_n = n + 1) :
    ∃ s' t, Exec w (alg99TailSortProg a r r_n) s s' t ∧
      t ≤ 100 * (n + G.numEdges + 1) ∧
      s'.arrs (a + 4) = List.ofFn (fun e : Fin G.toComputeDigraph.numEdges =>
        τ (G.computeToMultiEdgeEquiv e)) ∧
      (∀ b : ℕ, b ≠ a + 2 → b ≠ a + 3 → b ≠ a + 4 → s'.arrs b = s.arrs b) ∧
      (∀ j : ℕ, j ≠ r → j ≠ r + 1 → j ≠ r + 2 → s'.regs j = s.regs j) := by
  have hkeys' : s.arrs a = (alg99TailKeys G).map Fin.val := by
    rw [alg99TailKeys_eq_ofFn]
    simpa only [List.map_ofFn, Function.comp_def, Fin.val_castSucc] using hkeys
  obtain ⟨s', t, hex, ht, hlen, hout, ha, hr⟩ :=
    alg99TailSortProg_exec (alg99TailKeys G) (List.ofFn τ) a r r_n hw hn
      (by simpa using hm) (by simp)
      (by intro v hv; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv; exact hτ i)
      s hkeys' hvals hrn
  refine ⟨s', t, hex, ?_, ?_, ha, hr⟩
  · simp only [length_alg99TailKeys] at ht
    omega
  · apply List.ext_getElem (by simpa [MultiDigraph.toComputeDigraph] using hlen)
    intro j hj hj'
    have hje : j < G.toComputeDigraph.numEdges := by simpa using hj'
    let e : Fin G.toComputeDigraph.numEdges := ⟨j, hje⟩
    have h := hout ⟨(G.computeToMultiEdgeEquiv e).1, by simp⟩
    rw [alg99BucketPosition_computeToMultiEdgeEquiv, List.getD_eq_getElem _ _ hj] at h
    simpa only [List.getElem_ofFn, e] using h

end GraphMinor.Compute
