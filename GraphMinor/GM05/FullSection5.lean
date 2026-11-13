module

public import GraphMinor.GM05.ConnectedTransfer
public import GraphMinor.GM05.PathTransfer
public import GraphMinor.GM05.Section5
import GraphMinor.Minor.Basic

/-!
# Meshes in graphs with loops and parallel edges

A mesh imposes only connectivity, vertex disjointness within each family,
and vertex intersections between the families. Taking the shadow preserves
all these conditions. Paths selected in a branch subgraph lift as vertex
sequences in that same subgraph.
-/

@[expose] public section
namespace GraphMinor.GM05.Full
open Graph GM01
variable {α β : Type*}

/-- Graph Minors V, Section 5, page 100: two families of connected subgraphs,
disjoint within each family, with every member of one meeting every member
of the other. Unlike a web, a mesh allows common edges. -/
structure IsMesh (G : Graph α β) {m n : ℕ}
    (A : Fin m → Graph α β) (B : Fin n → Graph α β) : Prop where
  le_left : ∀ i, A i ≤ G
  le_right : ∀ j, B j ≤ G
  connected_left : ∀ i, GraphConnected (A i)
  connected_right : ∀ j, GraphConnected (B j)
  disjoint_left : Pairwise fun i j => Disjoint V(A i) V(A j)
  disjoint_right : Pairwise fun i j => Disjoint V(B i) V(B j)
  meets : ∀ i j, (V(A i) ∩ V(B j)).Nonempty

/-- Taking shadows preserves a mesh, including its vertex sets. -/
theorem IsMesh.shadow {G : Graph α β} {m n : ℕ}
    {A : Fin m → Graph α β} {B : Fin n → Graph α β} (h : IsMesh G A B) :
    GM05.IsMesh (simpleShadow G) (fun i => simpleShadow (A i))
      (fun j => simpleShadow (B j)) :=
  ⟨fun i => simpleShadow_mono (h.le_left i),
    fun j => simpleShadow_mono (h.le_right j),
    fun i => (graphConnected_iff_simpleShadow_connected _).mp (h.connected_left i),
    fun j => (graphConnected_iff_simpleShadow_connected _).mp (h.connected_right j),
    h.disjoint_left, h.disjoint_right, h.meets⟩

/-- Graph Minors V, (5.2), page 101, for hosts with loops and parallel edges.
Select `p` branch paths and `q` members of the other family to obtain a
smaller mesh. The path conditions specify the mesh by its vertex sets.
`GM05.theorem_5_2_simple` is the simple-host version. -/
theorem theorem_5_2_proof {G : Graph α β} {θ p q : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hp : 2 ≤ p) (hq : 2 ≤ q)
    {A : Fin (p * ((θ ^ 2 / 2) ^ (q - 1)).choose q +
      (θ ^ 2 / 2) * ((θ ^ 2 / 2) ^ (q - 1)).choose (θ ^ 2 / 2)) → Graph α β}
    {B : Fin ((θ ^ 2 / 2) ^ (q - 1)) → Graph α β} (hm : IsMesh G A B) :
    ∃ (embI : Fin p ↪ Fin (p * ((θ ^ 2 / 2) ^ (q - 1)).choose q +
        (θ ^ 2 / 2) * ((θ ^ 2 / 2) ^ (q - 1)).choose (θ ^ 2 / 2)))
      (embJ : Fin q ↪ Fin ((θ ^ 2 / 2) ^ (q - 1))) (P : Fin p → Path α),
      (∀ i, PathIsIn (P i) (A (embI i))) ∧
      Pairwise (fun i j => Disjoint (P i).verts (P j).verts) ∧
      (∀ j, B (embJ j) ≤ G ∧ GraphConnected (B (embJ j))) ∧
      Pairwise (fun i j => Disjoint V(B (embJ i)) V(B (embJ j))) ∧
      ∀ i j, ((P i).verts ∩ V(B (embJ j))).Nonempty := by
  obtain ⟨embI, embJ, P, hP, hmesh⟩ := GM05.theorem_5_2_simple hθ heven hV
    (fun h => hno (h.trans (simpleShadow_isIsoMinor G hV hE))) hp hq hm.shadow
  exact ⟨embI, embJ, P, fun i => pathIsIn_iff.mpr (hP i),
    hmesh.disjoint_left, fun j => ⟨hm.le_right _, hm.connected_right _⟩,
    hmesh.disjoint_right, hmesh.meets⟩

/-- Graph Minors V, (5.3), page 102, for hosts with loops and parallel edges.
A grid-excluding graph has no mesh of the specified size.
`GM05.theorem_5_3_simple` is the simple-host version. -/
theorem theorem_5_3_proof {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) :
    ¬ ∃ (A : Fin (θ₅ θ) → Graph α β) (B : Fin (θ₆ θ) → Graph α β), IsMesh G A B := by
  rintro ⟨A, B, hm⟩
  exact GM05.theorem_5_3_simple hθ heven hV
    (fun h => hno (h.trans (simpleShadow_isIsoMinor G hV hE)))
    ⟨_, _, hm.shadow⟩

end GraphMinor.GM05.Full
