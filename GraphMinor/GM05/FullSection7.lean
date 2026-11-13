module

import GraphMinor.Minor.Basic

public import GraphMinor.GM05.FullTreeWidth
public import GraphMinor.GM05.Section7

/-!
# Balanced separators and width bounds for arbitrary finite graphs

Excluding the grid passes to the simple shadow. Vertex separations and bag
widths transfer back without changing any vertex counts.
-/

public section
namespace GraphMinor.GM05.Full
open Graph GM01
variable {α β : Type*}

private theorem shadow_no_grid {G : Graph α β} {θ : ℕ}
    (hV : V(G).Finite) (hE : E(G).Finite) (hno : ¬ IsIsoMinor (gridGraph θ) G) :
    simpleShadow G ∈ 𝓕 θ :=
  fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE))

/-- Graph Minors V, (7.1), page 106, for hosts with loops and parallel edges.
A graph excluding the grid has a small balanced vertex separation.
`GM05.theorem_7_1_simple` is the simple-host version. -/
theorem theorem_7_1_proof {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) :
    ∃ A B : Set α, IsSeparation G A B ∧ (A ∩ B).ncard ≤ θ₇ θ ∧
      θ₈ θ * (A \ B).ncard ≤ (θ₈ θ - 1) * V(G).ncard ∧
      θ₈ θ * (B \ A).ncard ≤ (θ₈ θ - 1) * V(G).ncard := by
  obtain ⟨A, B, hsep, hrest⟩ :=
    GM05.theorem_7_1_simple hθ heven hV (shadow_no_grid hV hE hno)
  exact ⟨A, B, isSeparation_iff.mpr hsep, hrest⟩

/-- Graph Minors V, (7.2), page 107, for hosts with loops and parallel edges.
The separator balances any prescribed vertex set `X`.
`GM05.theorem_7_2_simple` is the simple-host version. -/
theorem theorem_7_2_proof {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) {X : Set α} (hX : X ⊆ V(G)) :
    ∃ A B : Set α, IsSeparation G A B ∧ (A ∩ B).ncard ≤ θ₇ θ ∧
      θ₈ θ * ((A \ B) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard ∧
      θ₈ θ * ((B \ A) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard := by
  obtain ⟨A, B, hsep, hrest⟩ :=
    GM05.theorem_7_2_simple hθ heven hV (shadow_no_grid hV hE hno) hX
  exact ⟨A, B, isSeparation_iff.mpr hsep, hrest⟩

/-- Graph Minors V, (7.3), page 108, for hosts with loops and parallel edges.
Excluding the grid bounds tree-width by `θ₉ θ`.
`GM05.theorem_7_3_simple` is the simple-host version. -/
theorem theorem_7_3_proof {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) : TreeWidthLE G (θ₉ θ) :=
  treeWidthLE_iff.mpr (GM05.theorem_7_3_simple hθ heven hV (shadow_no_grid hV hE hno))

end GraphMinor.GM05.Full
