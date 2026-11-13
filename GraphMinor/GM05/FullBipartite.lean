module

public import GraphMinor.GM05.ConnectedTransfer
public import GraphMinor.GM05.EdgeTransfer
public import GraphMinor.GM05.Section4Bipartite
import GraphMinor.Minor.Basic

/-!
# A complete bipartite configuration in an arbitrary finite graph

Take the shadows of the connected branch subgraphs. Their vertex sets and
disjointness stay the same. Edges between disjoint branch sets cannot be loops.
-/

public section
namespace GraphMinor.GM05.Full
open Graph GM01
variable {α β : Type*}

/-- Graph Minors V, (4.1), page 97, for hosts with loops and parallel edges.
A grid-excluding graph cannot contain the indicated large complete bipartite
configuration. `GM05.theorem_4_1_simple` is the simple-host version. -/
theorem theorem_4_1_proof {G : Graph α β} {θ m n : ℕ}
    (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (A : Fin m → Graph α β) (B : Fin n → Graph α β)
    (hA : ∀ i, A i ≤ G) (hB : ∀ j, B j ≤ G)
    (hcA : ∀ i, GraphConnected (A i)) (hcB : ∀ j, GraphConnected (B j))
    (hdA : Pairwise fun i j => Disjoint V(A i) V(A j))
    (hdB : Pairwise fun i j => Disjoint V(B i) V(B j))
    (hdAB : ∀ i j, Disjoint V(A i) V(B j))
    (hadj : ∀ i j, ∃ x ∈ V(A i), ∃ y ∈ V(B j), G.Adj x y) :
    m < θ ^ 2 / 2 ∨ n < θ ^ 2 / 2 := by
  apply GM05.theorem_4_1_simple heven hV
    (fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE)))
    (fun i => simpleShadow (A i)) (fun j => simpleShadow (B j))
    (fun i => simpleShadow_mono (hA i)) (fun j => simpleShadow_mono (hB j))
    (fun i => (graphConnected_iff_simpleShadow_connected _).mp (hcA i))
    (fun j => (graphConnected_iff_simpleShadow_connected _).mp (hcB j)) hdA hdB hdAB
  intro i j
  obtain ⟨x, hx, y, hy, hxy⟩ := hadj i j
  exact ⟨x, hx, y, hy, fun heq => Set.disjoint_left.mp (hdAB i j) hx (heq.symm ▸ hy), hxy⟩

/-- Graph Minors V, (4.2), page 97, for hosts with loops and parallel edges.
The connected subgraphs `B j` use disjoint actual edge sets, their prescribed
intersection vertices have actual valency one, and the host has maximum
valency four. The conclusion is the printed bound `n < θ₁ θ`.
`GM05.theorem_4_2_simple` is the simple-host version. The proof uses the same
counting argument, with incident edges paying for shadow neighbor counts. -/
theorem theorem_4_2_proof {G : Graph α β} {θ n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G)
    (A : Fin (θ ^ 2 / 2) → Graph α β) (B : Fin n → Graph α β)
    (hA : ∀ i, A i ≤ G) (hcA : ∀ i, GraphConnected (A i))
    (hdA : Pairwise fun i j => Disjoint V(A i) V(A j))
    (hB : ∀ j, B j ≤ G) (hcB : ∀ j, GraphConnected (B j))
    (hdB : Pairwise fun i j => Disjoint E(B i) E(B j))
    (hAB : ∀ i j, ∃ x, V(A i) ∩ V(B j) = {x} ∧ IsLeafOf (B j) x)
    (hdeg : ∀ x ∈ V(G), valency G x ≤ 4) : n < θ₁ θ := by
  apply GM05.card_lt_thetaOne_of_neighbor_sum_le_four hθ heven hV
    (fun hm => hno (hm.trans (simpleShadow_isIsoMinor G hV hE)))
    (fun i => simpleShadow (A i)) (fun j => simpleShadow (B j))
    (fun i => simpleShadow_mono (hA i))
    (fun i => (graphConnected_iff_simpleShadow_connected _).mp (hcA i)) hdA
    (fun j => simpleShadow_mono (hB j))
    (fun j => (graphConnected_iff_simpleShadow_connected _).mp (hcB j))
  · intro i j
    obtain ⟨x, hv, hl⟩ := hAB i j
    exact ⟨x, hv, hl.shadow⟩
  · intro x hx
    exact (sum_shadow_neighbors_le_valency hV hE B hB hdB x).trans (hdeg x hx)

end GraphMinor.GM05.Full
