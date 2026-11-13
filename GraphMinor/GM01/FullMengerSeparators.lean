module

public import GraphMinor.GM01.FullPathFamilies
import GraphMinor.GM01.MengerSeparators

/-!
# The clean-path or small-cut alternative for general graphs

Apply the simple theorem to the shadow. In the path alternative choose actual
edges for each path. Their vertex sequences are unchanged, so disjointness,
endpoints and internal avoidance survive. In the cut alternative transfer the
vertex separators back to the original graph.
-/

public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- **Graph Minors I, (2.9)** (pages 49–50):
"If $B_1, \dots, B_n$ are disjoint connected subgraphs of a graph $G \in \mathscr{F}_\theta$, and
$V' \subseteq V(G)$ and $r \ge 0$ is an integer, then one of the following is true:
(i) there exists $J \subseteq \{1, \dots, n\}$ with $|J| = r$ such that for each $j \in J$ there is
a path $P_j$ in $G$ from $B_j$ to $V'$, and the paths $P_j$ ($j \in J$) are disjoint, and each has
no internal vertex in $V' \cup \bigcup_{j \in J} V(B_j)$;"
"(ii) there exist $X \subseteq V(G)$ and $J \subseteq \{1, \dots, n\}$ with
$|X| + |J| \le 2^{r\theta^4}$, such that $X$ separates $V'$ from every $B_j$
($j \in \{1, \dots, n\} - J$)."
This is the general-graph form. The simple special case is `GM01.theorem_2_9_simple`. -/
theorem theorem_2_9_proof {θ r n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G)
    {V' : Set α} (hV' : V' ⊆ V(G))
    (B : Fin n → Graph α β) (hB : ∀ j, B j ≤ G)
    (hconn : ∀ j, GraphConnected (B j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j)) :
    (∃ (J : Set (Fin n)) (P : J → Path α β),
      J.ncard = r ∧
      (∀ j : J, (P j).IsFromTo G V(B j.1) V') ∧
      Pairwise (fun i j : J ↦ Disjoint (P i).verts (P j).verts) ∧
      (∀ j : J, Disjoint (P j).toPath.internalVerts (V' ∪ ⋃ j' ∈ J, V(B j')))) ∨
    (∃ (X : Set α) (J : Set (Fin n)),
      X ⊆ V(G) ∧ X.ncard + J.ncard ≤ 2 ^ (r * θ ^ 4) ∧
      ∀ j ∉ J, Separates G X V' V(B j)) := by
  classical
  obtain hpaths | hcut := GM01.theorem_2_9_simple (r := r) hθ heven hV
    (shadow_mem_gridFree hV hE hG) hV' (fun j ↦ simpleShadow (B j))
    (fun j ↦ simpleShadow_mono (hB j))
    (fun j ↦ (graphConnected_iff_simpleShadow_connected _).mp (hconn j)) hBD
  · obtain ⟨J, Q, hJ, hQ, hQD, hQI⟩ := hpaths
    have hlift : ∀ j, ∃ P : Path α β, P.IsIn G ∧ P.toPath = Q j :=
      fun j ↦ Path.exists_lift (hQ j).1
    choose P hP hPQ using hlift
    left
    refine ⟨J, P, hJ, ?_, ?_, ?_⟩
    · intro j
      refine ⟨hP j, ?_⟩
      rw [hPQ j]
      exact (hQ j).2
    · intro i j hij
      change Disjoint (P i).toPath.verts (P j).toPath.verts
      rw [hPQ i, hPQ j]
      exact hQD hij
    · intro j
      rw [hPQ j]
      exact hQI j
  · obtain ⟨X, J, hX, hcard, hsep⟩ := hcut
    exact Or.inr ⟨X, J, hX, hcard, fun j hj ↦ separates_iff.mpr (hsep j hj)⟩

end GraphMinor.GM01.Full
