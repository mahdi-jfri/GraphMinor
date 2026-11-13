module

public import GraphMinor.GM01.Defs
import GraphMinor.GM05.Section5

/-!
# Two families of connected subgraphs

Graph Minors I, (2.10), announces a result to be proved in Graph Minors V.
The mesh bound in Graph Minors V, (5.3), supplies it. We restrict both
families to the sizes in that bound. The proof of (5.3) uses only results
already proved in the library.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

universe u

/-- Graph Minors I, (2.10), page 50: two sufficiently large disjoint families
of connected subgraphs of a grid-excluding graph have a disjoint pair, one
from each family. The paper announces the proof in Graph Minors V. Here we
apply its (5.3), page 102, with its cited (3.1) and (4.3) already proved. -/
theorem theorem_2_10_simple {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    ∃ n : ℕ, 0 < n ∧ ∀ {α : Type u} (G : (⊤ : SimpleGraph α).Subgraph),
      G.verts.Finite → G ∈ 𝓕 θ →
      ∀ (A B : Fin n → (⊤ : SimpleGraph α).Subgraph),
        (∀ i, A i ≤ G) → (∀ j, B j ≤ G) →
        (∀ i, (A i).Connected) → (∀ j, (B j).Connected) →
        (Pairwise fun i j ↦ Disjoint (A i).verts (A j).verts) →
        (Pairwise fun i j ↦ Disjoint (B i).verts (B j).verts) →
        ∃ i j, Disjoint (A i).verts (B j).verts := by
  classical
  let n := max (GM05.θ₅ θ) (GM05.θ₆ θ) + 1
  refine ⟨n, Nat.zero_lt_succ _, ?_⟩
  intro α G hfin hG A B hA hB hAc hBc hAd hBd
  by_contra h
  have hmeet : ∀ i j, ((A i).verts ∩ (B j).verts).Nonempty := by
    intro i j
    exact Set.not_disjoint_iff.mp (fun hd ↦ h ⟨i, j, hd⟩)
  have hleft : GM05.θ₅ θ ≤ n := (Nat.le_max_left _ _).trans (Nat.le_succ _)
  have hright : GM05.θ₆ θ ≤ n := (Nat.le_max_right _ _).trans (Nat.le_succ _)
  exact GM05.theorem_5_3_simple hθ heven hfin hG
    ⟨A ∘ Fin.castLE hleft, B ∘ Fin.castLE hright,
      { le_left := fun i ↦ hA _
        le_right := fun j ↦ hB _
        connected_left := fun i ↦ hAc _
        connected_right := fun j ↦ hBc _
        disjoint_left := fun i j hij ↦ hAd ((Fin.castLE_injective hleft).ne hij)
        disjoint_right := fun i j hij ↦ hBd ((Fin.castLE_injective hright).ne hij)
        meets := fun i j ↦ hmeet _ _ }⟩

end GraphMinor.GM01
