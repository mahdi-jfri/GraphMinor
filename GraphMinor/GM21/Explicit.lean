module

public import GraphMinor.GM21.Final
public import GraphMinor.GM21.Section10

/-!
# Explicit bound for Graph Minors XXI, (1.1)

This file provides the explicit tree-width bound `theorem_1_1_bound V p` and the explicit
theorem `theorem_1_1_explicit` for **Graph Minors XXI, (1.1)**, parameterized by an arbitrary
upper bound `V` on `GM07.vModel`. Separating this from `GraphMinor/GM21/Final.lean` keeps
`GraphMinor.GM21.Section10` a private import of `Final.lean`.
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14

universe u v

namespace Final

/-- Explicit tree-width bound for **Graph Minors XXI, (1.1)**, parameterized by an upper bound `V`
on `GM07.vModel`. -/
def theorem_1_1_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (p : ℕ) : ℕ :=
  (3 * theorem_10_4_bound V p) / 2

/-- Explicit version of `hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage` with bound
`theorem_1_1_bound V p`. -/
theorem hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (p : ℕ) :
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β),
      G.IsGraph → GM21.HasVitalPLinkage G p → treeWidthPlusOne G ≤ theorem_1_1_bound V p + 1 := by
  dsimp only [theorem_1_1_bound]
  set θ := theorem_10_4_bound V p
  intro α β G hG hvit
  have h104 := theorem_10_4_explicit.{u, v} V hV p (α := α) (β := β)
  by_cases htw0 : treeWidthPlusOne G = 0
  · omega
  · have htw_pos : 1 ≤ treeWidthPlusOne G := Nat.pos_of_ne_zero htw0
    let w_G := treeWidthPlusOne G - 1
    have hw_G : treeWidthPlusOne G = w_G + 1 := by omega
    obtain ⟨⟨θ_G, 𝒯, h𝒯, hge⟩, _⟩ := theorem_3_1_proof G w_G hw_G
    have hlt : θ_G < θ := by
      by_contra hge_θ
      exact h104 G θ_G 𝒯 hG (Nat.le_of_not_lt hge_θ) h𝒯 hvit
    omega

/-- Explicit version of **Graph Minors XXI, (1.1)** (Section 1, page 1 of the preprint) with
tree-width bound `theorem_1_1_bound V p`. -/
theorem theorem_1_1_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (p : ℕ) :
    ∀ {α : Type u} {β : Type v} (G L : Graph α β),
      V(G).Finite → E(G).Finite → IsVitalPLinkage G L p → TreeWidthLE G (theorem_1_1_bound V p) := by
  intro α β G L hVG hEG hvit
  apply treeWidthLE_of_treeWidthPlusOne_le hVG hEG
  exact hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage_explicit.{u, v} V hV p
    (Hypergraph.ofGraph G hVG hEG) (GM16.isGraph_ofGraph G hVG hEG)
    (hasVitalPLinkage_ofGraph hVG hEG hvit)

end Final

export Final (theorem_1_1_bound theorem_1_1_explicit)

end GraphMinor.GM21
