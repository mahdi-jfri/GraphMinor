module

public import GraphMinor.GM01.RootedModelVertices
import Mathlib.Data.Finset.Max

/-!
# Choosing a maximum represented comb length

In the positive-height proof used for Graph Minors I, (1.1), page 55,
choose `N` maximum such that the rooted target has a model of `P(γ,N)`.
The model vertex embedding bounds every such length by the finite target
vertex count. We take the maximum of this finite nonempty set of lengths.
-/

public section

namespace GraphMinor.GM01

open Graph

universe u v

/-- The maximum-length choice on page 55 in the proof of Graph Minors I,
(1.1). An existing comb model makes the set of positive represented
lengths nonempty, and the proved vertex bound makes it finite. -/
theorem exists_max_rootedPathComb {α : Type u} {β : Type v}
    (G : RootedGraph α β) (hfin : V(G.graph).Finite) {γ μ : ℕ} (hμ : 0 < μ)
    (hmodel : HasRootedMinor (rootedPathComb γ μ hμ) G) :
    ∃ N : ℕ, μ ≤ N ∧ ∃ hN : 0 < N,
      HasRootedMinor (rootedPathComb γ N hN) G ∧
      ∀ n (hn : 0 < n), HasRootedMinor (rootedPathComb γ n hn) G → n ≤ N := by
  classical
  let S : Set ℕ := {n | ∃ hn : 0 < n, HasRootedMinor (rootedPathComb γ n hn) G}
  have hsub : S ⊆ (Finset.range (V(G.graph).ncard + 1) : Set ℕ) := by
    rintro n ⟨hn, ⟨M⟩⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (M.pathComb_length_le hn G hfin))
  have hSfin : S.Finite := (Finset.finite_toSet _).subset hsub
  let s := hSfin.toFinset
  have hsnonempty : s.Nonempty := ⟨μ, hSfin.mem_toFinset.mpr ⟨hμ, hmodel⟩⟩
  let N := s.max' hsnonempty
  have hNmem : N ∈ S := hSfin.mem_toFinset.mp (Finset.max'_mem s hsnonempty)
  have hmax (n : ℕ) (hn : n ∈ S) : n ≤ N :=
    Finset.le_max' s n (hSfin.mem_toFinset.mpr hn)
  obtain ⟨hN, hNmodel⟩ := hNmem
  exact ⟨N, hmax μ ⟨hμ, hmodel⟩, hN, hNmodel,
    fun n hn hmodeln ↦ hmax n ⟨hn, hmodeln⟩⟩

end GraphMinor.GM01
