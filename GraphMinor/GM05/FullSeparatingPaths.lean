module

public import GraphMinor.GM05.PathTransfer
public import GraphMinor.GM05.Quoted
import GraphMinor.Minor.Basic

/-!
# Disconnected separators of a family of disjoint paths

Paths and vertex separators transfer to the simple shadow. The component
count of each given subgraph is represented by its shadow, as in (1.6).
-/

public section
namespace GraphMinor.GM05.Full
open Graph GM01
variable {α β : Type*}

/-- Graph Minors V, (4.3), page 98, for hosts with loops and parallel edges,
with the same correction `0 < d + n` as the simple-host version
`GM05.theorem_4_3_simple`. Bound a disjoint family of separators of disjoint paths. -/
theorem theorem_4_3_proof {G : Graph α β} {θ m n d : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hpos : 0 < d + n)
    (hV : V(G).Finite) (hE : E(G).Finite) (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (A B : Set α) (hA : A ⊆ V(G)) (hB : B ⊆ V(G))
    (D : Fin m → Graph α β) (hle : ∀ i, D i ≤ G)
    (hd : Pairwise fun i j => Disjoint V(D i) V(D j))
    (hcomp : ∀ i, numComponents (simpleShadow (D i)) ≤ d)
    (hpaths : ∃ P : Fin n → Path α,
      (∀ i, PathFromTo (P i) G A B) ∧
      Pairwise (fun i j => Disjoint (P i).verts (P j).verts))
    (hsep : ∀ i, Separates G V(D i) A B) :
    n < d * θ ^ 2 / 2 ∨ m < 2 ^ (d * θ ^ 2 / 2) * (θ ^ 2 + 2 * d * θ ^ (2 * θ)) := by
  simp_rw [pathFromTo_iff] at hpaths
  simp_rw [separates_iff] at hsep
  exact GM05.theorem_4_3_simple hθ heven hpos hV
    (fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE)))
    A B hA hB (fun i => simpleShadow (D i))
    (fun i => simpleShadow_mono (hle i)) hd hcomp hpaths hsep

end GraphMinor.GM05.Full
